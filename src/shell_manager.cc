#include "shell_manager.hh"

#include "debug.hh"
#include "client.hh"
#include "clock.hh"
#include "context.hh"
#include "command_manager.hh"
#include "display_buffer.hh"
#include "event_manager.hh"
#include "face_registry.hh"
#include "option_manager.hh"
#include "file.hh"
#include "flags.hh"
#include "option_types.hh"
#include "regex.hh"

#include <chrono>
#include <cstring>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#include <cstdlib>
#include <errno.h>

#if defined(__CYGWIN__) || defined(__APPLE__)
#define vfork fork
#endif

extern char **environ;

namespace Kakoune
{

ShellManager::ShellManager(ConstArrayView<EnvVarDesc> builtin_env_vars)
    : m_env_vars{builtin_env_vars}
{
    auto is_executable = [](StringView path) {
        struct stat st;
        if (stat(path.zstr(), &st))
            return false;

        bool executable = (st.st_mode & S_IXUSR)
                        | (st.st_mode & S_IXGRP)
                        | (st.st_mode & S_IXOTH);
        return S_ISREG(st.st_mode) and executable;
    };

    if (const char* shell = getenv("KAKOUNE_POSIX_SHELL"))
    {
        if (not is_executable(shell))
            throw runtime_error{format("KAKOUNE_POSIX_SHELL '{}' is not executable", shell)};
        m_shell = shell;
    }
    else // Get a guaranteed to be POSIX shell binary
    {
        #if defined(_CS_PATH)
        auto size = confstr(_CS_PATH, nullptr, 0);
        String path; path.resize(size-1, 0);
        confstr(_CS_PATH, path.data(), size);
        #else
        StringView path = "/bin:/usr/bin";
        #endif
        for (auto dir : StringView{path} | split<StringView>(':'))
        {
            auto candidate = format("{}/sh", dir);
            if (is_executable(candidate))
            {
                m_shell = std::move(candidate);
                break;
            }
        }
        if (m_shell.empty())
            throw runtime_error{format("unable to find a posix shell in {}", path)};
    }

    // Add Kakoune binary location to the path to guarantee that %sh{ ... }
    // have access to the kak command regardless of if the user installed it
    {
        const char* path = getenv("PATH");
        auto new_path = format("{}../libexec/kak:{}", split_path(get_kak_binary_path()).first, path);
        setenv("PATH", new_path.c_str(), 1);
    }
}

namespace
{

Shell spawn_shell(const char* shell, StringView cmdline,
                  ConstArrayView<String> params,
                  ConstArrayView<String> kak_env,
                  bool open_stdin) noexcept
{
    Vector<const char*> envptrs;
    for (char** envp = environ; *envp; ++envp)
        envptrs.push_back(*envp);
    for (auto& env : kak_env)
        envptrs.push_back(env.c_str());
    envptrs.push_back(nullptr);

    auto cmdlinezstr = cmdline.zstr();
    Vector<const char*> execparams = { "sh", "-c", cmdlinezstr };
    if (not params.empty())
        execparams.push_back(shell);
    for (auto& param : params)
        execparams.push_back(param.c_str());
    execparams.push_back(nullptr);

    auto make_pipe = []() -> Array<UniqueFd, 2> {
        if (int pipefd[2] = {-1, -1}; ::pipe(pipefd) == 0)
            return {UniqueFd{pipefd[0]}, UniqueFd{pipefd[1]}};
        throw runtime_error(format("unable to create pipe, errno: {}", ::strerror(errno)));
    };

    auto stdin_pipe = open_stdin ? make_pipe() : Array{UniqueFd{open("/dev/null", O_RDONLY)}, UniqueFd{}};
    auto stdout_pipe = make_pipe();
    auto stderr_pipe = make_pipe();
    if (pid_t pid = vfork())
        return {pid, std::move(stdin_pipe[1]), std::move(stdout_pipe[0]), std::move(stderr_pipe[0])};

    constexpr auto renamefd = [](int oldfd, int newfd) {
        if (oldfd == newfd)
            return;
        dup2(oldfd, newfd);
        close(oldfd);
    };

    renamefd((int)stdin_pipe[0], 0);
    renamefd((int)stdout_pipe[1], 1);
    renamefd((int)stderr_pipe[1], 2);

    close((int)stdin_pipe[1]);
    close((int)stdout_pipe[0]);
    close((int)stderr_pipe[0]);

    execve(shell, (char* const*)execparams.data(), (char* const*)envptrs.data());
    char buffer[1024];
    write(STDERR_FILENO, format_to(buffer, "execve failed: {}\n", strerror(errno)));
    _exit(-1);
    return {-1, {}, {}, {}};
}

template<typename GetValue>
Vector<String> generate_env(StringView cmdline, ConstArrayView<String> params, const Context& context, GetValue&& get_value)
{
    static const Regex re(R"(\bkak_(quoted_)?(\w+)\b)");

    Vector<String> env;
    auto add_matches = [&](StringView s) {
        for (auto&& match : RegexIterator{s.begin(), s.end(), re})
        {
            StringView name{match[2].first, match[2].second};
            StringView shell_name{match[0].first, match[0].second};

            auto match_name = [&](const String& s) {
                return s.substr(0_byte, shell_name.length()) == shell_name and
                       s.substr(shell_name.length(), 1_byte) == "=";
            };
            if (any_of(env, match_name))
                continue;

            try
            {
                StringView quoted{match[1].first, match[1].second};
                Quoting quoting = match[1].matched ? Quoting::Shell : Quoting::Raw;
                env.push_back(format("kak_{}{}={}", quoted, name, get_value(name, quoting)));
            } catch (runtime_error&) {}
        }
    };
    add_matches(cmdline);
    for (auto&& param : params)
        add_matches(param);

    return env;
}

FDWatcher make_reader(int fd, EventMode mode, String& contents,
                      MoveOnlyFunction<void (FDWatcher& watcher, int error)> on_close)
{
    return {fd, FdEvents::Read, mode,
            [&contents, on_close = std::move(on_close)](FDWatcher& watcher, FdEvents, EventMode) {
        const int fd = watcher.fd();
        char buffer[1024];
        while (fd_readable(fd))
        {
            ssize_t size = ::read(fd, buffer, sizeof(buffer));
            if (size <= 0)
            {
                if (size < 0 and errno == EAGAIN)
                    continue; // try again

                const int error = size < 0 ? errno : 0;
                watcher.disable();
                on_close(watcher, error);
                return;
            }
            contents += StringView{buffer, buffer+size};
        }
    }};
}

FDWatcher make_pipe_writer(UniqueFd& fd, const FunctionRef<StringView ()>& generator)
{
    int flags = fcntl((int)fd, F_GETFL, 0);
    fcntl((int)fd, F_SETFL, flags | O_NONBLOCK);
    return {(int)fd, FdEvents::Write, EventMode::Urgent,
            [&generator, &fd, contents=generator()](FDWatcher& watcher, FdEvents, EventMode) mutable {
        while (fd_writable((int)fd))
        {
            ssize_t size = ::write((int)fd, contents.begin(),
                                   (size_t)contents.length());
            if (size > 0)
            {
                contents = contents.substr(ByteCount{(int)size});
                if (contents.empty())
                    contents = generator();
            }
            if (size == -1 and (errno == EAGAIN or errno == EWOULDBLOCK))
                return;
            if (size < 0 or contents.empty())
            {
                fd.close();
                watcher.disable();
                return;
            }
        }
    }};
}

struct CommandFifos
{
    String base_dir;
    String command;
    UniqueFd command_fd;

    CommandFifos()
      : base_dir(format("{}/kak-fifo.XXXXXX", tmpdir()))
    {
        if (mkdtemp(base_dir.data()) == nullptr or
            mkfifo(command_fifo_path().c_str(), 0600) != 0 or
            mkfifo(response_fifo_path().c_str(), 0600) != 0)
            throw runtime_error(format("unable to create command/response fifos, errno: {}", ::strerror(errno)));

        command_fd = UniqueFd{open(command_fifo_path().c_str(), O_RDONLY | O_NONBLOCK)};
    }

    ~CommandFifos()
    {
        // it it important that we unlink the command_fifo *before* we close
        // the command_fd (through the destructor of UniqueFd). This ensures
        // that a writer to the fifo will either get ENOENT because the fifo
        // was unlinked or EPIPE/SIGPIPE because the other end of an open
        // command fifo closed.
        unlink(command_fifo_path().c_str());
        unlink(response_fifo_path().c_str());
        rmdir(base_dir.c_str());
    }

    // Calls execute with each command written to the command fifo, a command
    // ends once the fifo is closed by all its writers.
    FDWatcher watch(EventMode mode, MoveOnlyFunction<void (StringView command)> execute)
    {
        return make_reader((int)command_fd, mode, command,
                           [this, execute = std::move(execute)](FDWatcher& watcher, int error) {
            if (error != 0)
            {
                write_to_debug_buffer(format("error reading from command fifo '{}'", strerror(error)));
                return;
            }

            auto rearm = OnScopeEnd([&] {
                command.clear();
                // The fifo keeps reporting eof until another writer opens it,
                // reopen it to wait for that writer. The previous descriptor
                // gets closed after the new one is opened so that the fifo
                // always has a reader.
                command_fd = UniqueFd{open(command_fifo_path().c_str(), O_RDONLY | O_NONBLOCK)};
                if (not command_fd)
                    write_to_debug_buffer(format("error reopening command fifo '{}'", strerror(errno)));
                watcher.reset_fd((int)command_fd);
            });

            execute(command);
        });
    }

    String command_fifo_path() const { return format("{}/command-fifo", base_dir); }
    String response_fifo_path() const { return format("{}/response-fifo", base_dir); }
};

}

// A background job is what remains of a shell command whose stderr is still
// open once its stdout got closed. Until that stderr gets closed, it is
// forwarded to the debug buffer and the command fifo keeps accepting commands.
struct ShellManager::BackgroundJob
{
    BackgroundJob(UniqueFd err, UniquePtr<CommandFifos> fifos)
      : m_err{std::move(err)}, m_fifos{std::move(fifos)},
        m_fifo_watcher{m_fifos ? new FDWatcher(m_fifos->watch(EventMode::Normal, execute)) : nullptr},
        m_err_watcher{(int)m_err, FdEvents::Read, EventMode::Normal,
                      [this](FDWatcher&, FdEvents, EventMode) { read_stderr(); }}
    {
    }

    String debug_description() const
    {
        if (not m_fifos)
            return format("stderr fd: {}", (int)m_err);
        return format("stderr fd: {}\ncommand fd: {}\nfifo directory: {}",
                      (int)m_err, (int)m_fifos->command_fd, m_fifos->base_dir);
    }

private:
    static void execute(StringView command)
    {
        try
        {
            Context context{Context::EmptyContextFlag{}};
            CommandManager::instance().execute(command, context);
        }
        catch (const runtime_error& error)
        {
            write_to_debug_buffer(format("error running command '{}': {}", command, error.what()));
        }
    }

    void read_stderr()
    {
        const int fd = (int)m_err;
        char buffer[1024];
        while (fd_readable(fd))
        {
            ssize_t size = ::read(fd, buffer, sizeof(buffer));
            if (size < 0 and errno == EAGAIN)
                continue; // try again

            if (size <= 0)
            {
                report_stderr(m_err_contents.length());
                ShellManager::instance().remove_background_job(this);
                return; // this got destroyed
            }
            m_err_contents += StringView{buffer, buffer+size};
        }

        // only report complete lines
        ByteCount end = m_err_contents.length();
        while (end > 0 and m_err_contents[end-1] != '\n')
            --end;
        report_stderr(end);
    }

    void report_stderr(ByteCount count)
    {
        if (count == 0)
            return;
        write_to_debug_buffer(format("shell stderr: <<<\n{}>>>", m_err_contents.substr(0_byte, count)));
        m_err_contents = m_err_contents.substr(count).str();
    }

    UniqueFd m_err;
    String m_err_contents;
    UniquePtr<CommandFifos> m_fifos;
    UniquePtr<FDWatcher> m_fifo_watcher;
    FDWatcher m_err_watcher;
};

ShellManager::~ShellManager() = default;

void ShellManager::remove_background_job(BackgroundJob* job)
{
    auto it = find_if(m_background_jobs, [job](auto& j) { return j.get() == job; });
    kak_assert(it != m_background_jobs.end());
    m_background_jobs.erase(it);
}

void ShellManager::debug_background_jobs() const
{
    write_to_debug_buffer("Background jobs:");
    for (auto& job : m_background_jobs)
        write_to_debug_buffer(job->debug_description());
}

std::pair<String, int> ShellManager::eval(
    StringView cmdline, const Context& context, FunctionRef<StringView ()> input_generator,
    Flags flags, const ShellContext& shell_context)
{
    const DebugFlags debug_flags = context.options()["debug"].get<DebugFlags>();
    const bool profile = debug_flags & DebugFlags::Profile;
    if (debug_flags & DebugFlags::Shell)
        write_to_debug_buffer(format("shell:\n{}\n----\nargs: {}\n----\n", cmdline, join(shell_context.params | transform(shell_quote), ' ')));

    auto start_time = profile ? Clock::now() : Clock::time_point{};

    UniquePtr<CommandFifos> command_fifos;
    UniquePtr<FDWatcher> command_watcher;

    auto kak_env = generate_env(cmdline, shell_context.params, context, [&](StringView name, Quoting quoting) {
        if (name == "command_fifo" or name == "response_fifo")
        {
            if (not command_fifos)
            {
                command_fifos = make_unique_ptr<CommandFifos>();
                command_watcher.reset(new FDWatcher(command_fifos->watch(EventMode::Urgent, [&](StringView command) {
                    CommandManager::instance().execute(command, const_cast<Context&>(context), shell_context);
                })));
            }
            return name == "command_fifo" ?
                command_fifos->command_fifo_path() : command_fifos->response_fifo_path();
        }

        if (auto it = shell_context.env_vars.find(name); it != shell_context.env_vars.end())
            return it->value;
        return join(get_val(name, context) | transform(quoter(quoting)), ' ', false);
    });

    auto spawn_time = profile ? Clock::now() : Clock::time_point{};
    auto shell = spawn_shell(m_shell.c_str(), cmdline, shell_context.params, kak_env, true);
    auto wait_time = Clock::now();

    String stdout_contents, stderr_contents;
    auto stdout_reader = make_reader((int)shell.out, EventMode::Urgent, stdout_contents,
                                     [&](FDWatcher&, int){ shell.out.close(); });
    auto stderr_reader = make_reader((int)shell.err, EventMode::Urgent, stderr_contents,
                                     [&](FDWatcher&, int){ shell.err.close(); });
    auto stdin_writer = make_pipe_writer(shell.in, input_generator);

    // block SIGCHLD to make sure we wont receive it before
    // our call to pselect, that will end up blocking indefinitly.
    sigset_t mask, orig_mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGCHLD);
    sigprocmask(SIG_BLOCK, &mask, &orig_mask);
    auto restore_mask = OnScopeEnd([&] { sigprocmask(SIG_SETMASK, &orig_mask, nullptr); });

    int status = 0;
    // check for termination now that SIGCHLD is blocked
    bool terminated = waitpid((int)shell.pid, &status, WNOHANG) != 0;
    bool failed = false;

    using namespace std::chrono;
    BusyIndicator busy_indicator{context, [&](seconds elapsed) {
        return DisplayLine{format("waiting for shell command to finish{} ({}s)",
                                  terminated ? " (shell terminated)" : "", elapsed.count()),
                           context.faces()[failed ? "Error" : "Information"]};
    }};

    bool cancelling = false;
    while (not terminated or shell.in or
           ((flags & Flags::WaitForStdout) and shell.out))
    {
        try
        {
            EventManager::instance().handle_next_events(EventMode::Urgent, &orig_mask);
        }
        catch (cancel&)
        {
            kill((int)shell.pid, SIGINT);
            cancelling = true;
        }
        catch (runtime_error& error)
        {
            write_to_debug_buffer(format("error while waiting for shell: {}", error.what()));
            failed = true;
        }
        if (not terminated)
            terminated = waitpid((int)shell.pid, &status, WNOHANG) == (int)shell.pid;
    }

    if (not stderr_contents.empty())
        write_to_debug_buffer(format("shell stderr: <<<\n{}>>>", stderr_contents));

    if (profile)
    {
        auto end_time = Clock::now();
        auto full = duration_cast<microseconds>(end_time - start_time);
        auto spawn = duration_cast<microseconds>(wait_time - spawn_time);
        auto wait = duration_cast<microseconds>(end_time - wait_time);
        write_to_debug_buffer(format("shell execution took {} us (spawn: {}, wait: {})",
                                     (size_t)full.count(), (size_t)spawn.count(), (size_t)wait.count()));
    }

    if (cancelling)
        throw cancel{};

    if ((flags & Flags::WaitForStdout) and shell.err)
    {
        stderr_reader.disable();
        command_watcher.reset();
        m_background_jobs.push_back(make_unique_ptr<BackgroundJob>(std::move(shell.err), std::move(command_fifos)));
    }
    else if (command_fifos and not command_fifos->command.empty())
        write_to_debug_buffer(format("discarding unterminated command fifo content: <<<\n{}>>>", command_fifos->command));

    return { std::move(stdout_contents), WIFEXITED(status) ? WEXITSTATUS(status) : -1 };
}

Shell ShellManager::spawn(StringView cmdline, const Context& context,
                          bool open_stdin, const ShellContext& shell_context)
{
    auto kak_env = generate_env(cmdline, shell_context.params, context, [&](StringView name, Quoting quoting) {
        if (auto it = shell_context.env_vars.find(name); it != shell_context.env_vars.end())
            return it->value;
        return join(get_val(name, context) | transform(quoter(quoting)), ' ', false);
    });

    return spawn_shell(m_shell.c_str(), cmdline, shell_context.params, kak_env, open_stdin);
}

Vector<String> ShellManager::get_val(StringView name, const Context& context) const
{
    auto env_var = find_if(m_env_vars, [name](const EnvVarDesc& desc) {
        return desc.prefix ? prefix_match(name, desc.str) : name == desc.str;
    });

    if (env_var == m_env_vars.end())
        throw runtime_error("no such variable: " + name);

    return env_var->func(name, context);
}

CandidateList ShellManager::complete_env_var(StringView prefix,
                                             ByteCount cursor_pos) const
{
    return complete(prefix, cursor_pos,
                    m_env_vars | transform(&EnvVarDesc::str));
}

}

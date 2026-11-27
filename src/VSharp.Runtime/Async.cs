namespace VSharp.Runtime;

/// <summary>
/// Base of the state machine the compiler generates for an async function. The generated <see cref="Run"/> holds the
/// body: it dispatches on <see cref="State"/>, and at an 'await' whose task has not finished it saves its locals,
/// records where to resume and calls <see cref="Schedule"/>. Continuations do not capture the synchronization
/// context, so a caller that blocks on the task cannot deadlock.
/// </summary>
public abstract class AsyncMachine
{
    public int State;
    internal Completion Done = null!;
    private Action? _next;

    /// <summary>Runs the body from <see cref="State"/> until it completes or suspends.</summary>
    public abstract void Run();

    public void MoveNext()
    {
        try
        {
            Run();
        }
        catch (Exception e)
        {
            Done.Fail(e);
        }
    }

    /// <summary>Resumes the machine when <paramref name="task"/> finishes. The caller returns right after.</summary>
    public void Schedule(Task task) => task.ConfigureAwait(false).GetAwaiter().UnsafeOnCompleted(_next ??= MoveNext);
}

internal abstract class Completion
{
    public abstract void Fail(Exception e);
}

internal sealed class Completion<T> : Completion
{
    public readonly TaskCompletionSource<T> Source = new(TaskCreationOptions.RunContinuationsAsynchronously);
    public override void Fail(Exception e) => Source.TrySetException(e);
}

/// <summary>The calls generated code makes into an <see cref="AsyncMachine"/>; generic, so they work for any result type.</summary>
public static class Async
{
    public static Task<T> Start<T>(AsyncMachine m)
    {
        var c = new Completion<T>();
        m.Done = c;
        m.MoveNext();
        return c.Source.Task;
    }

    public static Task StartUnit(AsyncMachine m) => Start<bool>(m);

    /// <summary>The value first, so generated code can push it before the machine.</summary>
    public static void Complete<T>(T value, AsyncMachine m) => ((Completion<T>)m.Done).Source.TrySetResult(value);

    public static void CompleteUnit(AsyncMachine m) => Complete(true, m);

    public static T Result<T>(Task<T> task) => task.GetAwaiter().GetResult();

    public static void Wait(Task task) => task.GetAwaiter().GetResult();

    /// <summary>The entry point for an async 'main'.</summary>
    public static void RunMain(Task task) => task.GetAwaiter().GetResult();
}

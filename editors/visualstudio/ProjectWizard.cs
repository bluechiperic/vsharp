#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using EnvDTE;
using Microsoft.VisualStudio.TemplateWizard;

namespace VSharp.VisualStudio;

/// <summary>
/// Copies the V# MSBuild SDK to a stable folder when a project is created, and writes the project's first source file.
/// </summary>
public sealed class ProjectWizard : IWizard
{
    public const string SdkFolderName = "Sdk";

    private bool _newProject;
    private string? _safeName;
    private string? _destination;

    public void RunStarted(object automationObject, Dictionary<string, string> replacementsDictionary, WizardRunKind runKind, object[] customParams)
    {
        if (runKind == WizardRunKind.AsNewItem)
            return;

        _newProject = true;
        _safeName = Value(replacementsDictionary, "$safeprojectname$");
        _destination = Value(replacementsDictionary, "$destinationdirectory$") ?? DirectoryFrom(customParams);
        CopySdk(ExtensionDirectory());
    }

    public void ProjectFinishedGenerating(Project project)
    {
        var directory = Path.GetDirectoryName(project.FullName);
        if (!string.IsNullOrEmpty(directory))
            _destination = directory;
        var file = WriteStarter(_destination, _safeName);
        AddFile(project, file);
    }

    public void ProjectItemFinishedGenerating(ProjectItem projectItem) { }

    public bool ShouldAddProjectItem(string filePath) => true;

    public void BeforeOpeningFile(ProjectItem projectItem) { }

    public void RunFinished()
    {
        if (_newProject)
            WriteStarter(_destination, _safeName);
    }

    /// <summary>Writes the starter module if the template host did not leave the .vs file behind.</summary>
    private static string? WriteStarter(string? directory, string? module)
    {
        if (string.IsNullOrEmpty(directory) || string.IsNullOrEmpty(module))
            return null;
        Directory.CreateDirectory(directory);
        var path = Path.Combine(directory, module + ".vs");
        if (!File.Exists(path))
        {
            File.WriteAllText(path,
                "module " + module + Environment.NewLine + Environment.NewLine +
                "fn hello() -> Int" + Environment.NewLine +
                "  ensures result == 1" + Environment.NewLine +
                "{" + Environment.NewLine +
                "  return 1" + Environment.NewLine +
                "}" + Environment.NewLine);
        }
        return path;
    }

    private static void AddFile(Project? project, string? path)
    {
        if (project == null || string.IsNullOrEmpty(path) || !File.Exists(path))
            return;
        try { project.ProjectItems.AddFromFile(path); }
        catch (Exception ex) when (ex is System.Runtime.InteropServices.COMException or InvalidOperationException or NotImplementedException)
        {
        }
    }

    private static string? Value(Dictionary<string, string> replacements, string key) =>
        replacements.TryGetValue(key, out var value) && !string.IsNullOrWhiteSpace(value) ? value : null;

    private static string? DirectoryFrom(object[] customParams)
    {
        if (customParams == null)
            return null;
        foreach (var param in customParams)
        {
            if (param is string path && path.Length > 0 && Directory.Exists(path))
                return path;
        }
        return null;
    }

    /// <summary>Copies Sdk.props and Sdk.targets from the extension into %LOCALAPPDATA%\Microsoft\VisualStudio\VSharp\Sdk.</summary>
    public static string CopySdk(string extensionDirectory)
    {
        var source = Path.Combine(extensionDirectory, SdkFolderName);
        var destination = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData),
            "Microsoft", "VisualStudio", "VSharp", SdkFolderName);
        Directory.CreateDirectory(destination);
        foreach (var name in new[] { "Sdk.props", "Sdk.targets" })
        {
            var from = Path.Combine(source, name);
            if (!File.Exists(from))
                throw new FileNotFoundException("The V# extension is missing its MSBuild SDK. Reinstall the extension.", from);
            File.Copy(from, Path.Combine(destination, name), overwrite: true);
        }
        return destination;
    }

    private static string ExtensionDirectory()
    {
        var assembly = typeof(ProjectWizard).Assembly;
        var path = assembly.Location;
        if (string.IsNullOrEmpty(path))
        {
#pragma warning disable CS0618 // CodeBase is the fallback when the extension assembly is shadow-copied.
            path = assembly.CodeBase == null ? "" : new Uri(assembly.CodeBase).LocalPath;
#pragma warning restore CS0618
        }
        var directory = Path.GetDirectoryName(path);
        if (string.IsNullOrEmpty(directory))
            throw new InvalidOperationException("Could not find the V# extension folder.");
        return directory;
    }

}

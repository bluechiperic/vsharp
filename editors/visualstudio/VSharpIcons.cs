#nullable enable
using System;
using System.ComponentModel.Composition;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;
using Microsoft.VisualStudio.ProjectSystem;
using Microsoft.Win32;

namespace VSharp.VisualStudio;

/// <summary>
/// Puts the V# mark on the project node and on .vs files in Solution Explorer.
/// </summary>
[Export(typeof(IProjectTreePropertiesProvider))]
[AppliesTo("VSharp")]
[Order(1000)]
public sealed class VSharpIcons : IProjectTreePropertiesProvider
{
    internal static readonly Guid ImageGuid = new Guid("A7C3E1D4-5B28-4F90-8C16-2D9E0A4B7F31");

    private const int FileImageId = 2;

    private static readonly ProjectImageMoniker ProjectIcon = new ProjectImageMoniker(ImageGuid, 1);
    private static readonly ProjectImageMoniker FileIcon = new ProjectImageMoniker(ImageGuid, FileImageId);

    static VSharpIcons()
    {
        try
        {
            RegisterExplorerIcon();
        }
        catch (Exception)
        {
            // Explorer keeps whatever icon it already has.
        }
    }

    public void CalculatePropertyValues(IProjectTreeCustomizablePropertyContext propertyContext, IProjectTreeCustomizablePropertyValues propertyValues)
    {
        if (propertyValues.Flags.Contains(ProjectTreeFlags.ProjectRoot))
        {
            propertyValues.Icon = ProjectIcon;
            propertyValues.ExpandedIcon = ProjectIcon;
            return;
        }

        if (propertyContext.IsFolder)
            return;

        var name = propertyContext.ItemName;
        if (name != null && name.EndsWith(".vs", StringComparison.OrdinalIgnoreCase))
            propertyValues.Icon = FileIcon;
        else if (name != null && name.EndsWith(".vsharpproj", StringComparison.OrdinalIgnoreCase))
            propertyValues.Icon = ProjectIcon;
    }

    private static void RegisterExplorerIcon()
    {
        var directory = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
        if (string.IsNullOrEmpty(directory))
            return;

        var source = Path.Combine(directory, "Resources", "vsharp-file.ico");
        if (!File.Exists(source))
            return;

        var destinationDir = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData),
            "Microsoft",
            "VisualStudio",
            "VSharp");
        Directory.CreateDirectory(destinationDir);
        var destination = Path.Combine(destinationDir, "vsharp-file.ico");
        File.Copy(source, destination, true);

        var icon = "\"" + destination + "\",0";
        using (var extension = Registry.CurrentUser.CreateSubKey(@"Software\Classes\.vs"))
            extension?.SetValue("", "VSharp.Source");
        using (var extensionIcon = Registry.CurrentUser.CreateSubKey(@"Software\Classes\.vs\DefaultIcon"))
            extensionIcon?.SetValue("", icon);
        using (var fileType = Registry.CurrentUser.CreateSubKey(@"Software\Classes\VSharp.Source"))
            fileType?.SetValue("", "V# Source");
        using (var fileIcon = Registry.CurrentUser.CreateSubKey(@"Software\Classes\VSharp.Source\DefaultIcon"))
            fileIcon?.SetValue("", icon);

        var launcher = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.ProgramFilesX86),
            "Common Files",
            "Microsoft Shared",
            "MSEnv",
            "VSLauncher.exe");
        if (File.Exists(launcher))
        {
            using (var command = Registry.CurrentUser.CreateSubKey(@"Software\Classes\VSharp.Source\shell\open\command"))
                command?.SetValue("", "\"" + launcher + "\" \"%1\"");
        }

        SHChangeNotify(0x08000000, 0x0000, IntPtr.Zero, IntPtr.Zero);
    }

    [DllImport("shell32.dll")]
    private static extern void SHChangeNotify(int eventId, uint flags, IntPtr item1, IntPtr item2);
}

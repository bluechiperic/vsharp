# V# for Visual Studio

Syntax highlighting and project support for [V#](https://github.com/bluechiperic/vsharp) in Visual Studio 2022 and Visual Studio 2026.

`.vs` files use the same grammar as the VS Code extension: keywords, contracts, effects, typed holes, and string interpolation. `//` comments toggle, and brackets match. `.vs` files and `.vsharpproj` projects use the V# icon.

`.vsharpproj` files open in Solution Explorer and build with MSBuild. Build runs `vsharpc build` on every `.vs` file in the project and writes `<AssemblyName>.dll` under `bin\<Configuration>`. A failed proof is a build error, with the source span and the counterexample.

## A project

```xml
<Project>
  <PropertyGroup>
    <VSharpSdkRoot Condition="'$(VSharpSdkRoot)' == ''">$(MSBuildThisFileDirectory)..\..\sdk\VSharp.NET.Sdk\Sdk\</VSharpSdkRoot>
  </PropertyGroup>

  <Import Project="$(VSharpSdkRoot)Sdk.props" />

  <PropertyGroup>
    <AssemblyName>Hello</AssemblyName>
    <OutputType>Library</OutputType>
  </PropertyGroup>

  <Import Project="$(VSharpSdkRoot)Sdk.targets" />
</Project>
```

`VSharpSdkRoot` points at the directory that contains `Sdk.props` and `Sdk.targets`. In this repository that is `sdk/VSharp.NET.Sdk/Sdk`. The same files are installed with the extension, under its `Sdk` folder. The SDK imports Visual Studio's design-time targets when they are present, which is what lets Solution Explorer open the project.

`samples/hello/Hello.sln` is a project you can open. From that directory, `dotnet build` compiles it after the compiler itself has been built.

## New project and new file

After you install the extension and restart Visual Studio:

- **File → New → Project**, then choose **V# Project**. The project is a library with one proved function, `hello`.
- In Solution Explorer, **Add → New Item**, then choose **V# Module**. The new `.vs` file is named from the dialog, and its first line is `module` followed by that name.

Creating a project copies the MSBuild SDK to `%LOCALAPPDATA%\Microsoft\VisualStudio\VSharp\Sdk`. A project created inside this repository still uses `sdk/VSharp.NET.Sdk` when that folder is two levels above it. A project created anywhere else builds with `vsharpc` on `PATH`, or with `VSharpCompiler` set to `vsharpc.dll`.

The compiler is found in this order:

1. `$(VSharpCompiler)`, a path to `vsharpc.exe` or `vsharpc.dll`
2. `src/VSharp.Compiler/bin/<Configuration>/net10.0/vsharpc.dll` when the SDK is the copy in this repo
3. `vsharpc` on `PATH`

`VSharpVerify` defaults to `true`. Set it to `false` to skip proofs. `VSharpTotal` turns on overflow proofs. `VSharpReference` items are passed as `--reference`.

## Install

From this directory, on Windows:

```
dotnet build -c Release
```

The package is `bin\Release\net472\VSharp.VisualStudio.vsix`. Install it from that file, or with the Visual Studio installer:

```
VSIXInstaller.exe bin\Release\net472\VSharp.VisualStudio.vsix
```

Restart Visual Studio, then open `samples/hello/Hello.sln` and build it. This project is not part of `VSharp.sln`, because that solution is built on Linux and macOS and a Visual Studio extension is Windows-only.

`.vs` is also used by some shader tools for vertex shaders. If those files are highlighted as V#, set their Open With editor back to the shader editor.

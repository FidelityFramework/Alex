using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security;
using System.Text.RegularExpressions;
using Microsoft.Build.Framework;
using Microsoft.Build.Utilities;

namespace Alex.Boundary.Tasks
{
    public sealed class ValidateAlexBoundary : Task
    {
        private const int MaxSymlinkHops = 40;

        [Required]
        public ITaskItem[] Sources { get; set; } = Array.Empty<ITaskItem>();

        public ITaskItem[]? ProjectReferences { get; set; }

        [Required]
        public string Permitted { get; set; } = string.Empty;

        [Required]
        public string Scope { get; set; } = string.Empty;

        private static bool TryCanonicalPath(string raw, out string canonical, out string error)
        {
            canonical = string.Empty;
            error = string.Empty;
            if (string.IsNullOrWhiteSpace(raw))
            {
                error = "Path is empty or whitespace.";
                return false;
            }

            try
            {
                var normalized = raw.Replace('\\', Path.DirectorySeparatorChar);
                // Collapse lexical '.' and '..' segments before symlink walking so
                // MSBuild relative paths (e.g. $(MSBuildThisFileDirectory)../BAREWire/...)
                // resolve identically to MSBuild FullPath even across non-sibling symlink targets.
                var rooted = Path.GetFullPath(normalized);
                var root = Path.GetPathRoot(rooted) ?? string.Empty;
                var pending = new Queue<string>(
                    rooted.Substring(root.Length)
                        .Split(new[] { Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar }, StringSplitOptions.RemoveEmptyEntries));

                var current = root;
                var hops = 0;
                while (pending.Count > 0)
                {
                    var segment = pending.Dequeue();
                    if (segment == ".")
                        continue;

                    if (segment == "..")
                    {
                        var trimmed = current.TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
                        var parent = Path.GetDirectoryName(trimmed);
                        current = string.IsNullOrEmpty(parent) ? root : parent;
                        continue;
                    }

                    var candidate = Path.Combine(current, segment);
                    FileSystemInfo? target = null;
                    if (Directory.Exists(candidate))
                    {
                        target = new DirectoryInfo(candidate).ResolveLinkTarget(returnFinalTarget: true);
                    }
                    else if (File.Exists(candidate))
                    {
                        target = new FileInfo(candidate).ResolveLinkTarget(returnFinalTarget: true);
                    }
                    else
                    {
                        var dangling = new FileInfo(candidate).LinkTarget;
                        if (dangling != null)
                        {
                            error = $"Unresolvable or cyclic symbolic link '{candidate}' -> '{dangling}'.";
                            return false;
                        }
                    }

                    if (target != null)
                    {
                        if (hops >= MaxSymlinkHops)
                        {
                            error = $"Symbolic link resolution exceeded {MaxSymlinkHops} hops at '{candidate}'.";
                            return false;
                        }

                        hops++;
                        var resolved = target.FullName;
                        var resolvedRoot = Path.GetPathRoot(resolved) ?? string.Empty;
                        var nextQueue = new Queue<string>(
                            resolved.Substring(resolvedRoot.Length)
                                .Split(new[] { Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar }, StringSplitOptions.RemoveEmptyEntries));
                        while (pending.Count > 0)
                            nextQueue.Enqueue(pending.Dequeue());
                        current = resolvedRoot;
                        pending = nextQueue;
                        continue;
                    }

                    current = candidate;
                }

                canonical = Path.GetFullPath(current);
                return true;
            }
            catch (IOException ex)
            {
                error = ex.Message;
                return false;
            }
            catch (UnauthorizedAccessException ex)
            {
                error = ex.Message;
                return false;
            }
            catch (SecurityException ex)
            {
                error = ex.Message;
                return false;
            }
            catch (ArgumentException ex)
            {
                error = ex.Message;
                return false;
            }
        }

        public override bool Execute()
        {
            var compilerService = new Regex(@"\bClef\s*\.\s*Compiler\b|\bFSharp\s*\.\s*Compiler\b");
            var targetEmission = new Regex(@"(?:->\s*|sprintf\s*|RawMLIR\s*\(?\s*)""[^""]*(?:!llvm[.<]|\bllvm\.[A-Za-z_])");
            var rewriteMarkers = new[] {
                "MLIRNanopass", "declarationCollectionPass", "relocateDefinition",
                "--load-pass-plugin", "--load-dialect-plugin", "--load-plugin",
                "FIDELITY_MLIR_PLUGINS", "mlir-plugins"
            };
            var processMarkers = new[] { "--pass-pipeline", "System.Diagnostics.Process", "ProcessStartInfo" };
            var markers = Scope == "library" ? rewriteMarkers.Concat(processMarkers).ToArray() : rewriteMarkers;

            foreach (var item in Sources)
            {
                var path = Path.GetFullPath(item.ItemSpec);
                var lines = File.ReadAllLines(path);
                for (var index = 0; index < lines.Length; index++)
                {
                    var line = lines[index];
                    if (Scope == "library" && !line.TrimStart().StartsWith("//", StringComparison.Ordinal) && targetEmission.IsMatch(line))
                        Log.LogError(null, "ALEX004", null, path, index + 1, 0, 0, 0,
                            "LLVM dialect emission belongs to backend realization, never Alex portable output.");
                    if (compilerService.IsMatch(line))
                        Log.LogError(null, "ALEX001", null, path, index + 1, 0, 0, 0,
                            "Alex reads a published PSG revision only. This line names the compiler service.");
                    foreach (var marker in markers)
                        if (line.IndexOf(marker, StringComparison.Ordinal) >= 0)
                            Log.LogError(null, "ALEX003", null, path, index + 1, 0, 0, 0,
                                "Prohibited rewrite, process or plugin entry '{0}'. Alex witnesses settled facts and emits once.", marker);
                }
            }

            var comparer = OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
            var permitted = new HashSet<string>(comparer);
            foreach (var rawPermitted in Permitted.Split(new[] { ';' }, StringSplitOptions.RemoveEmptyEntries))
            {
                if (!TryCanonicalPath(rawPermitted, out var canonicalPermitted, out var permittedError))
                {
                    Log.LogError(null, "ALEX002", null, rawPermitted, 0, 0, 0, 0,
                        "Failed to canonicalize permitted project path '{0}': {1}", rawPermitted, permittedError);
                }
                else
                {
                    permitted.Add(canonicalPermitted);
                }
            }

            if (ProjectReferences != null)
            {
                foreach (var reference in ProjectReferences)
                {
                    var itemPath = reference.GetMetadata("FullPath");
                    var rawRef = string.IsNullOrEmpty(itemPath) ? reference.ItemSpec : itemPath;
                    if (!TryCanonicalPath(rawRef, out var path, out var refError))
                    {
                        Log.LogError(null, "ALEX002", null, rawRef, 0, 0, 0, 0,
                            "Failed to canonicalize project reference '{0}': {1}", rawRef, refError);
                    }
                    else if (!permitted.Contains(path))
                    {
                        Log.LogError(null, "ALEX002", null, path, 0, 0, 0, 0,
                            "Alex references the published PSG contract and the library the contract references. No other project is permitted.");
                    }
                }
            }

            return !Log.HasLoggedErrors;
        }
    }
}

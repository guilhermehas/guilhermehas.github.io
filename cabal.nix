{ mkDerivation, base, directory, extra, filepath, hakyll, lib
, pandoc, process
}:
mkDerivation {
  pname = "guilherme-blog";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    base directory extra filepath hakyll pandoc process
  ];
  license = "unknown";
  hydraPlatforms = lib.platforms.none;
}

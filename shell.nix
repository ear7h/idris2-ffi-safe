{ pkgs ? import <nixpkgs> {} } : let

  testLib = pkgs.runCommandCC "testLib" {}
  (
    if pkgs.stdenv.isDarwin
    then
      ''
        mkdir -p $out/lib
        cc -dynamiclib -o $out/lib/libffisafe_test.dylib ${ ./test/lib.c }
      ''
    else
      ''
        mkdir -p $out/lib
        cc -shared -fPIC -o $out/lib/libffisafe_test.so ${ ./test/lib.c }
      ''
  );

  idris2-ear7h = (pkgs.idris2.unwrapped.overrideAttrs (old: {
    src = pkgs.fetchgit {
      url  = "https://github.com/ear7h/idris2";
      rev  = "f38c0ad";
      hash = "sha256-2NStzz8xpOR9SeuVHvxSWVor9YNTbDGfJMnDd/UV04c=";
    };
  })).withPackages (x: [ ]);

  libPath = with pkgs; lib.makeLibraryPath [
    testLib
  ];
in pkgs.mkShell {
  IDRIS2_SH =
    if pkgs.stdenv.hostPlatform.isDarwin
    then "${pkgs.coreutils}/bin/env DYLD_LIBRARY_PATH=${ libPath } ${pkgs.bash}/bin/sh"
    else "/bin/sh";

  LD_LIBRARY_PATH = libPath;
  # DYLD_LIBRARY_PATH = libPath;

  buildInputs = with pkgs; [
    idris2-ear7h
    chez
  ] ++ (pkgs.lib.optional pkgs.stdenv.hostPlatform.isLinux pkgs.valgrind);
}

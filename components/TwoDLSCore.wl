(* Standalone 2D-LS has a separate package context and configuration.
   The local_search sources differ from the recorded sources only by a
   reversible translation of the three package namespace prefixes. *)
Block[{$ContextPath = {"System`"}},
If[! MemberQ[$Packages, "PaperMCSAT`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "MCSATCore.wl"}]]];
If[! MemberQ[$Packages, "TwoDLSCore`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "local_search", "PaperSolvers.wl"}]]];
];

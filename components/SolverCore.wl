(* Hybrid solver implementation and its original local-search baseline.
   Keep package exports off the caller's context path; public tools use fully
   qualified names, so loading another tool cannot shadow these definitions. *)
Block[{$ContextPath = {"System`"}},
If[! MemberQ[$Packages, "PaperMCSAT`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "MCSATCore.wl"}]]];
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "hybrid", "PaperSolvers.wl"}]]];
];

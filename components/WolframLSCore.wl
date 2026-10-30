(* Compatibility loader for the Wolfram Language LS baseline. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "SolverCore.wl"}]]];

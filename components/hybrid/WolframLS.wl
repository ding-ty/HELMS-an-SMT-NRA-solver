(* Generated from the hash-bound Mathematica LS closure in HELMS.wl.
   The supplied original is preserved. No MCSAT/CAD fallback is included. *)
BeginPackage["PaperWolframLS`"];
PaperWolframLS`SolveLS::usage="SolveLS[polynomials,pairCNF,variables,config] runs the actual source-derived Wolfram LS.";
Begin["`Private`"];

pp=1;sp=0.003;cntLS=0;calculatedIsolation=<||>;
$Engineering=False;$SampleCache=<||>;$LastModel=<||>;$RestartCount=0;
$OriginalP={};$OriginalC={};$OriginalV={};
EvalValues[p_,a_] := If[TrueQ[$Engineering],PaperSolvers`Private`ExactPolynomialValues[p,a],p/.a];
FullModelQ[a_] := AssociationQ[a] && PaperSolvers`ModelQ[$OriginalP,$OriginalC,$OriginalV,a];
SharedWeightUpdate[p_,c_,a_,w_] := Module[{old,new,result=w},
  old=Lookup[w,c];new=PaperSolvers`Private`Reweight[p,c,a,old,sp];
  MapThread[(result[#1]+= #2-#3)&,{c,new,old}];result];

PaperWolframLS`SolveLS[p_List,c_List,v_List,cfg_Association:<||>] := Join[
  solveInternal[p,c,v,cfg],<|"solver_metadata"-><|
    "baseline_profile"->"source_derived_wolfram_ls",
    "vendor_sha256"->"f52bd891f1b83097f4fcac14c69145642e3970ef527fcc9ae4e775daf2c0ad23",
    "ls_wl_restarts"->Lookup[cfg,"ls_wl_restarts",8],
    "jump_limit"->If[Lookup[cfg,"ls_wl_jump_limit",Infinity]===Infinity,"Infinity",Lookup[cfg,"ls_wl_jump_limit",Infinity]],
    "initialization_policy"->"source IniMethodZero; IniMethodOne for restarts 2-6; IniMethodTwo from restart 7",
    "direction_policy"->"source gradients/current assignment/10 random integer vectors with original filtering",
    "tie_policy"->"source nearest sample and first minimum position; original sequential score update",
    "cycle_policy"->"source per-restart assignment cycle list",
    "sample_policy"->"source CountRoots/Root/IsolatingInterval width 10^-4 and Union; not paper-driver RootSamples",
    "open_cad_fallback"->False|>|>];

solveInternal[p_List,c_List,v_List,cfg_Association] := Block[
 {pp=Lookup[cfg,"l2o_delta",1],sp=Lookup[cfg,"weight_decrease_probability",0.003],
  cntLS=0,calculatedIsolation=<||>,$SampleCache=<||>,$RestartCount=0,
  $Engineering=TrueQ[Lookup[cfg,"engineering_optimizations",True]],
  $OriginalP=p,$OriginalC=c,$OriginalV=v,$LastModel=AssociationThread[v,ConstantArray[0,Length[v]]],
  PaperSolvers`Private`$EngineeringEnabled=TrueQ[Lookup[cfg,"engineering_optimizations",True]],
  PaperSolvers`Private`$CacheEnabled=TrueQ[Lookup[cfg,"cache_enabled",True]],
  PaperSolvers`Private`$CacheLimit=Lookup[cfg,"cache_max_entries",20000]},
 Module[{tag=Unique["LSInputExit"],restarts,limit,clauses={},kept,answer,model,failed=False},Catch[
  If[!DuplicateFreeQ[v] || !AllTrue[v,MatchQ[#,_Symbol]&] || !FreeQ[p,_Real] ||
     !AllTrue[p,PolynomialQ[#,v]&] || Complement[Variables[p],v]=!={} ||
     !AllTrue[c,ListQ] || !AllTrue[Flatten[c,1],MatchQ[#,{_Integer,1|-1}] && 1<=#[[1]]<=Length[p]&],
     Throw[<|"status"->"unknown","stage"->"LS-WL:invalid-input","assignment"->$LastModel,"num_jumps"->0|>,tag]];
  If[!TrueQ[pp>0],Throw[<|"status"->"unknown","stage"->"LS-WL:invalid-delta","assignment"->$LastModel,"num_jumps"->0|>,tag]];
  Scan[Function[clause,
    If[AnyTrue[clause,Variables[p[[#[[1]]]]]==={} && TrueQ[#[[2]]*p[[#[[1]]]]>0]&],Null,
      kept=Select[clause,Variables[p[[#[[1]]]]]=!={}&];
      If[kept==={},Throw[<|"status"->"unknown","stage"->"LS-WL:constant-conflict","assignment"->$LastModel,"num_jumps"->0|>,tag]];
      AppendTo[clauses,kept]]],c];
  If[clauses==={},If[FullModelQ[$LastModel],
    Throw[<|"status"->"sat","stage"->"LS-WL:constants","assignment"->$LastModel,"num_jumps"->0|>,tag]]];
  restarts=Lookup[cfg,"ls_wl_restarts",8];limit=Lookup[cfg,"ls_wl_jump_limit",Infinity];
  If[!IntegerQ[restarts] || restarts<1 || !(limit===Infinity || (IntegerQ[limit] && limit>=0)),
    Throw[<|"status"->"unknown","stage"->"LS-WL:invalid-budget","assignment"->$LastModel,"num_jumps"->0|>,tag]];
  answer=Check[LSSolver[p,clauses,v,restarts,limit],failed=True;$Failed];
  model=If[ListQ[answer] && Length[answer]>=3 && AssociationQ[answer[[3]]],answer[[3]],$LastModel];
  model=Join[AssociationThread[v,ConstantArray[0,Length[v]]],model];
  <|"status"->If[!failed && ListQ[answer] && Length[answer]>=1 && answer[[1]]==="sat" && FullModelQ[model],"sat","unknown"],
    "stage"->If[failed,"LS-WL:runtime-message","LS-WL"],"assignment"->model,
    "num_jumps"->cntLS,"restarts_attempted"->$RestartCount|>,tag]]
];
PaperWolframLS`SolveLS[___] := <|"status"->"unknown","stage"->"LS-WL:invalid-input","assignment"-><||>,"num_jumps"->0|>;

SatCheck[polyList_, cnf_, varList_, x_]:=
Module[{temp, polyValue, atomValue, clauseValue, cnfValue,functionExit=Unique["WolframLSExit"]},Catch[
	If[TrueQ[$Engineering],Throw[PaperSolvers`Private`LocalModelQ[polyList,cnf,varList,x],functionExit]];
 polyValue = EvalValues[polyList,x];
	atomValue = Function[{polyValue0, atom0}, Switch[atom0[[2]],
	-1, polyValue[[atom0[[1]]]]<0,
	0, polyValue[[atom0[[1]]]]==0,
	1, polyValue[[atom0[[1]]]]>0
	]];
	clauseValue = Function[{polyValue0, clause0}, Or @@ Map[atomValue[polyValue0, #]&, clause0]];
	cnfValue = Function[{polyValue0, cnf0}, And @@ Map[clauseValue[polyValue0, #]&, cnf0]];
	Throw[cnfValue[polyValue, cnf],functionExit];
,functionExit]];

SearchAndApplyOp1[polyList_, cnf_, varList_, varInterval_,  x_, w_]:=
Module[{atomInFalseClause, xNew=x, falseAtomInTrueClause, isCelljump=False,functionExit=Unique["WolframLSExit"]},Catch[
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x];
    Which[Length[atomInFalseClause] > 0,
        {isCelljump, xNew} = MaxScoreOp1[polyList, cnf, varList, varInterval,  x, w, atomInFalseClause];
        If[isCelljump,
            Throw[{isCelljump,  xNew},functionExit];
        ];
    ];
    falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x];
    Which[Length[falseAtomInTrueClause] > 0,
        {isCelljump, xNew} = MaxScoreOp1[polyList, cnf, varList, varInterval,  x, w, falseAtomInTrueClause];
    ];
    Throw[{isCelljump,  xNew},functionExit];
,functionExit]];

MaxScoreOp1[polyList_, cnf_, varList_, varInterval_,  x_, w_, atomList_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, isolation, tempx, distanceToX, xOld, xNew, maxScoreX, samplePoint, xVar,tempAtomList, isCelljump=False,functionExit=Unique["WolframLSExit"]},Catch[
	DistanceToTruth = Function[{atom0, x0},
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0,
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	Score = Function[{cnf0, x0, x1},
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
  If[TrueQ[$Engineering],Score=Function[{cnf0,x0,x1},
    PaperSolvers`Private`Loss[polyList,cnf0,x0,Lookup[w,cnf0],pp]-
    PaperSolvers`Private`Loss[polyList,cnf0,x1,Lookup[w,cnf0],pp]]];
	atomTruth = Function[atom0, Sign[(EvalValues[polyList,x])[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
    tempAtomList = falseAtomList;
	i = 0; maxScoreX = x; xOld = x;
	While[i <= Length[varList]-1,
		i++;
		tempx = x;
		tempx[varList[[i]]] = varList[[i]];
		falseAtomList=Select[tempAtomList,!FreeQ[polyList[[#[[1]]]],varList[[i]]]&];
        If[Length[falseAtomList]>0,
		    samplePoint = SamplePoint[polyList, falseAtomList, tempx];
        ,
            Continue[];
        ];
		j = 1;
		While[j <= Length[falseAtomList],
			Switch[falseAtomList[[j,2]],
			-1,
			xVar = Select[samplePoint[falseAtomList[[j]]], ((polyList[[falseAtomList[[j,1]]]]/.tempx)/.{varList[[i]]->#}) < 0 &];
			xVar = Select[xVar, Min[varInterval[varList[[i]]]]<#<Max[varInterval[varList[[i]]]] &];
			Which[xVar != {},
			distanceToX = Table[Abs[xVar[[k]] - x[varList[[i]]]], {k, Length[xVar]}];
			xNew =  x;
			xNew[varList[[i]]] = xVar[[Position[distanceToX, Min[distanceToX]][[1,1]]]];
			Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump=True;];
			],
			1,
			xVar = Select[samplePoint[falseAtomList[[j]]], ((polyList[[falseAtomList[[j,1]]]]/.tempx)/.{varList[[i]]->#}) > 0 &];
			xVar = Select[xVar, Min[varInterval[varList[[i]]]]<#<Max[varInterval[varList[[i]]]] &];
			Which[xVar != {},
			distanceToX = Table[Abs[xVar[[k]] - x[varList[[i]]]], {k, Length[xVar]}];
			xNew =  x;
			xNew[varList[[i]]] = xVar[[Position[distanceToX, Min[distanceToX]][[1,1]]]];
			Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump=True;];
			];
			];
			++j;
		];
	];
	Throw[{isCelljump, maxScoreX},functionExit];
,functionExit]];

RawSamplePoint[polyList_, atomList_, assign_]:=
Module[{i, j, poly, polyY, isoInterval, samplePoint, midPoint, ans, rootNum, LenDenNum, Y,functionExit=Unique["WolframLSExit"]},Catch[
	i = 1; ans= <||>;
	While[i <= Length[atomList],
		poly = (polyList[[atomList[[i,1]]]])/.assign;
		If[Length[Variables[Simplify[poly]]] == 0,
			samplePoint = {},
			polyY = poly/.<|(Variables[poly][[1]])->Y|>;
			If[TrueQ[PaperSolvers`Private`$CacheEnabled] && KeyExistsQ[calculatedIsolation,polyY],
				samplePoint = calculatedIsolation[polyY],
				rootNum = CountRoots[polyY,Y];
				If[rootNum==0,
					samplePoint = {1},
					isoInterval = IsolatingInterval[#,10^-4]&/@(Root[polyY,#]&/@Range[rootNum]);
					samplePoint = Flatten[isoInterval];
					If[Length[samplePoint]>0,
						midPoint = Table[(samplePoint[[2*i]] + samplePoint[[2*i+1]]) / 2, {i, Length[samplePoint]/2 - 1}];
						samplePoint = Union[{samplePoint[[1]]-1/10^4,samplePoint[[-1]]+1/10^4}, midPoint];
					];
					If[TrueQ[PaperSolvers`Private`$CacheEnabled] && Length[calculatedIsolation]<PaperSolvers`Private`$CacheLimit,calculatedIsolation[polyY]=samplePoint];
				];
			];
		];
        AppendTo[ans, atomList[[i]] -> samplePoint];
		++i;
    ];
	Throw[ans,functionExit];
,functionExit]];

GetAtomInFalseClause[polyList_, cnf_, varList_, x_]:=
Module[{SatAtom, SatClause, falseClause, atom,functionExit=Unique["WolframLSExit"]},Catch[
	SatAtom = Function[{atom0}, Sign[EvalValues[polyList,x][[atom0[[1]]]]] == Sign[atom0[[2]]] ];
	SatClause = Function[{clause0}, Or @@ Map[SatAtom[#]&, clause0]];
	falseClause = Select[cnf, SatClause[#] == False &];
	atom = Union @@ Map[falseClause[[#]]&, Range[Length[falseClause]]];
	Throw[atom,functionExit];
,functionExit]];

GetFalseAtomInTrueClause[polyList_, cnf_, varList_, x_]:=
Module[{SatAtom, SatClause, trueClause, atom, falseAtom,functionExit=Unique["WolframLSExit"]},Catch[
	SatAtom = Function[{atom0}, Sign[EvalValues[polyList,x][[atom0[[1]]]]] == Sign[atom0[[2]]] ];
	SatClause = Function[{clause0}, Or @@ Map[SatAtom[#]&, clause0]];
	trueClause = Select[cnf, SatClause[#] == True &];
	atom = Union @@ Map[trueClause[[#]]&, Range[Length[trueClause]]];
	falseAtom = Select[atom, SatAtom[#] == False &];
	Throw[falseAtom,functionExit];
,functionExit]];

UpdateWeight[polyList_, cnf_, varList_, x_, w_]:=
Module[{wNew, rand, SatAtom, SatClause, falseClause, trueClause, IncreaseWeight,functionExit=Unique["WolframLSExit"]},Catch[
	If[TrueQ[$Engineering],Throw[SharedWeightUpdate[polyList,cnf,x,w],functionExit]];
 wNew = w;
	rand = RandomReal[];
	SatAtom = Function[{atom0}, Sign[EvalValues[polyList,x][[atom0[[1]]]]] == Sign[atom0[[2]]] ];
	SatClause = Function[{clause0}, Or @@ Map[SatAtom[#]&, clause0]];
	falseClause = Select[cnf, SatClause[#] == False &];
	trueClause = Select[cnf, SatClause[#] == True && w[#] > 1 &];
	Which[rand >= sp, Scan[wNew[#] += 1 &, falseClause],
	True,Scan[wNew[#] -= 1 &, trueClause]];
	Throw[wNew,functionExit];
,functionExit]];

GradSearchAndApplyOp1[polyList_, cnf_, varList_, varInterval_,  x_, w_]:=
Module[{ZeroVecTest, ScalVecTest, gradVecList, i, currVec, RandVec, randvec, randVecList, direction, atomInFalseClause, falseAtomInTrueClause, xNew=x, isCelljump=False,functionExit=Unique["WolframLSExit"]},Catch[
	ZeroVecTest = Function[{vec}, And @@ Map[# == 0 &, vec]];
	ScalVecTest = Function[{vec, vecList}, i = SelectFirst[Range[Length[vec]], vec[[#]] != 0 &]; Or @@ Map[(#[[i]]/vec[[i]])*vec==#&, vecList]];
	gradVecList = Table[Map[D[polyList[[i]],#]&,varList]/.x, {i, Length[polyList]}];
	currVec = Table[x[varList[[i]]],{i,Length[varList]}];
	RandVec = Function[RandomInteger[{-1000, 1000}, Length[varList]]];
	randVecList = Table[RandVec[], {i,10}];
	direction = Union[gradVecList, {currVec}, randVecList];
	direction = Delete[direction, Select[Range[Length[direction]], Table[ZeroVecTest[direction[[i]]],{i,Length[direction]}][[#]]&]];
	direction = Delete[direction, Select[Table[{i},{i,Length[direction]}], ScalVecTest[direction[[#1[[1]]]], direction[[1;;#1[[1]]-1]]]&]];
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x];
    If[Length[atomInFalseClause] > 0,
        {isCelljump, xNew} = GradMaxScoreOp1[polyList, cnf, varList, varInterval,  x, w, atomInFalseClause, direction];
        If[isCelljump, Throw[{isCelljump, xNew},functionExit]];
    ];
    falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x];
    If[Length[falseAtomInTrueClause]>0,
        {isCelljump, xNew} = GradMaxScoreOp1[polyList, cnf, varList, varInterval,  x, w, falseAtomInTrueClause, direction];
    ];
    Throw[{isCelljump, xNew},functionExit];
,functionExit]];

GradMaxScoreOp1[polyList_, cnf_, varList_, varInterval_,  x_, w_, atomList_, direction_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, dir, polyListT, samplePoint,
	tVar, distanceTo0, tNew, xOld, xNew, maxScoreX, t, var, xVar, varnum=Length[varList], n, isCelljump=False,functionExit=Unique["WolframLSExit"]},Catch[
	DistanceToTruth = Function[{atom0, x0},
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0,
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	Score = Function[{cnf0, x0, x1},
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
  If[TrueQ[$Engineering],Score=Function[{cnf0,x0,x1},
    PaperSolvers`Private`Loss[polyList,cnf0,x0,Lookup[w,cnf0],pp]-
    PaperSolvers`Private`Loss[polyList,cnf0,x1,Lookup[w,cnf0],pp]]];
	atomTruth = Function[atom0, Sign[(EvalValues[polyList,x])[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	var = varList[[1]];
	i = 1; maxScoreX = x; xOld = x;
	While[i <= Length[direction],
		dir = direction[[i]];
		If[TrueQ[$Engineering],polyListT=ReplacePart[polyList,Normal[PaperSolvers`Private`RestrictPolynomials[polyList,DeleteDuplicates[First/@falseAtomList],Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * t, {k, Length[varList]}],False]]],polyListT = polyList/.Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * t, {k, Length[varList]}]];
		samplePoint = SamplePoint[polyListT, falseAtomList, <||>];
		j = 1;
		While[j <= Length[falseAtomList],
			Switch[falseAtomList[[j,2]],
				-1,
				tVar = Select[samplePoint[falseAtomList[[j]]], (polyListT[[falseAtomList[[j,1]]]]/.{t->#}) < 0 &];
				xVar = Table[Association[Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * tVar[[n]], {k, Length[varList]}]],{n,Length[tVar]}];
				n=1;
				While[n<=varnum,
					xVar = Select[xVar, Min[varInterval[varList[[n]]]]<#[varList[[n]]]<Max[varInterval[varList[[n]]]] &];
					n++;
				];
				Which[xVar != {},
				distanceTo0 = Table[Abs[(xVar[[k]])[var]-x[var]], {k, Length[xVar]}];
				xNew = xVar[[Position[distanceTo0, Min[distanceTo0]][[1,1]]]];
				Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump = True;];
				],
				1,
				tVar = Select[samplePoint[falseAtomList[[j]]], (polyListT[[falseAtomList[[j,1]]]]/.{t->#}) > 0 &];
				xVar = Table[Association[Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * tVar[[n]], {k, Length[varList]}]],{n,Length[tVar]}];
				n=1;
				While[n<=varnum,
					xVar = Select[xVar, Min[varInterval[varList[[n]]]]<#[varList[[n]]]<Max[varInterval[varList[[n]]]] &];
					n++;
				];
				Which[xVar != {},
				distanceTo0 = Table[Abs[(xVar[[k]])[var]-x[var]], {k, Length[xVar]}];
				xNew = xVar[[Position[distanceTo0, Min[distanceTo0]][[1,1]]]];
				Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump = True;];
				];
			];
			j++;
		];
		i++;
	];
	Throw[{isCelljump, maxScoreX},functionExit];
,functionExit]];

LSPreproc[polyList_,cnf_,varList_,linearList_,oneVarLinearList_] :=
Module[{init,varInterval,satAtomList,ans,functionExit=Unique["WolframLSExit"]},Catch[
  init=InitVarInterval[polyList,cnf,varList,oneVarLinearList];
  If[!ListQ[init] || Length[init]!=2 || !AssociationQ[init[[1]]],Throw[2,functionExit]];
  {varInterval,satAtomList}=init;
  ans=UsingOutInvPropClause[polyList,cnf,varList,varInterval,satAtomList,linearList,oneVarLinearList];
  If[!ListQ[ans] || Length[ans]<2,Throw[2,functionExit]];
  If[ans[[1]]===True,
    If[FullModelQ[ans[[2]]],Throw[ans,functionExit],Throw[{False,polyList,cnf,varList,varInterval},functionExit]]];
  If[ans[[1]]===False && Length[ans]>=3 && AssociationQ[ans[[3]]],
    Throw[{False,polyList,ans[[2]],varList,ans[[3]]},functionExit],Throw[2,functionExit]]
,functionExit]];

InitVarInterval[polyList_, cnf_, varList_, oneVarLinearList_]:=
Module[{i, satAtomList={}, varInterval, atom, clause, polyIndex, relaSign, poly,functionExit=Unique["WolframLSExit"]},Catch[
	varInterval = Association[Table[varList[[i]] -> Interval[{-Infinity, Infinity}], {i, Length[varList]}]];
	i=1;
	While[i<=Length[cnf],
		clause = cnf[[i]];
		If[Length[clause]==1,
			atom = clause[[1]];
			polyIndex = atom[[1]];
			If[MemberQ[oneVarLinearList, polyIndex],
				relaSign = atom[[2]];
				poly = polyList[[polyIndex]];
				varInterval = SolveOneVarLinear[poly, relaSign, varInterval];
				If[Length[varInterval]==0, Throw[False,functionExit]];
				AppendTo[satAtomList, atom];
			];
		];
		i++;
	];
	Throw[{varInterval, satAtomList},functionExit];
,functionExit]];

VarFixList[varList_, varInterval_]:=
Module[{varFixList,functionExit=Unique["WolframLSExit"]},Catch[
	varFixList = Select[Range[Length[varList]], Max[varInterval[varList[[#]]]]==Min[varInterval[varList[[#]]]] &];
	If[Length[varList]==Length[varFixList],
		Throw[False,functionExit];
	];
	Throw[varFixList,functionExit];
,functionExit]];

UsingOutInvPropClause[polyList_, cnf_, varList_, varInterval_, satAtomList_, linearList_, oneVarLinearList_]:=
Module[{i, clause, varInterval0 = varInterval, satAtomList0 = satAtomList, unsatAtomList0 = {}, ansCnf = {}, temp,functionExit=Unique["WolframLSExit"]},Catch[
	i=1;
	While[i<=Length[cnf],
		clause = cnf[[i]];
		temp = OutInvPropClause[clause, polyList, varList, varInterval0, satAtomList0, unsatAtomList0, linearList, oneVarLinearList];
		If[Length[temp]==0, Throw[False,functionExit]];
		If[Length[temp[[1]]]==0 && temp[[1]]==False,
			Throw[False,functionExit];
			,
			If[Length[temp[[1]]]==0 && temp[[1]]==True,
				varInterval0 = temp[[2]];
				satAtomList0 = temp[[3]];
				unsatAtomList0 = temp[[4]];
				,
				ansCnf = Join[ansCnf, {temp[[1]]}];
				varInterval0 = temp[[2]];
				satAtomList0 = temp[[3]];
				unsatAtomList0 = temp[[4]];
			];
		];
		i++;
	];
	If[Length[ansCnf]>0,
		Throw[{False, ansCnf, varInterval0},functionExit],
		Throw[{True, IniMethodZero[varList, varInterval0]},functionExit];
	];
,functionExit]];

OutInvPropClause[clause_, polyList_, varList_, varInterval_, satAtomList_, unsatAtomList_, linearList_, oneVarLinearList_]:=
Module[{i, unsatAtomNum=0, tempClause={}, atom, ans,functionExit=Unique["WolframLSExit"]},Catch[
	i=1;
	While[i<=Length[clause],
		atom = clause[[i]];
		If[MemberQ[satAtomList, atom],
			Throw[{True, varInterval, satAtomList, unsatAtomList},functionExit],
			If[MemberQ[unsatAtomList, atom],
				unsatAtomNum++,
				AppendTo[tempClause, atom];
			];
		];
		i++;
	];
	If[unsatAtomNum<Length[clause],
		ans = InvPropClause[tempClause, polyList, varList, varInterval, satAtomList, unsatAtomList, linearList, oneVarLinearList];
		If[Length[ans]==0, Throw[False,functionExit], Throw[ans,functionExit]];
		,
		Throw[{False, varInterval, satAtomList, unsatAtomList},functionExit];
	];
,functionExit]];

InvPropClause[newClause_, polyList_, varList_, varInterval_, satAtomList_, unsatAtomList_, linearList_, oneVarLinearList_]:=
Module[{i, ansVarInterval=varInterval, ansSatAtomList=satAtomList, ansUnsatAtomList=unsatAtomList, ansClause={}, atom, polyIndex, poly, relaSign, temp, flag=0,functionExit=Unique["WolframLSExit"]},Catch[
	i=1;
	While[i<=Length[newClause],
		atom = newClause[[i]];
		polyIndex = atom[[1]];
		poly = polyList[[polyIndex]];
		relaSign = atom[[2]];
		If[MemberQ[linearList, polyIndex],
			temp = InvPropLinearAtom[poly, relaSign, varList, ansVarInterval];
			If[temp==2,
				AppendTo[ansClause, atom],
				If[temp==1,
					AppendTo[ansSatAtomList, atom];Throw[{True,ansVarInterval,ansSatAtomList,ansUnsatAtomList},functionExit],
					If[Not[MemberQ[ansUnsatAtomList, atom]],
						AppendTo[ansUnsatAtomList, atom];
					];
				];
			],
			AppendTo[ansClause, atom];
		];
		i++;
	];
	If[Length[ansClause]==1,
		atom = ansClause[[1]];
		polyIndex = atom[[1]];
		If[MemberQ[oneVarLinearList, polyIndex],
			relaSign = atom[[2]];
			poly = polyList[[polyIndex]];
			ansVarInterval = SolveOneVarLinear[poly, relaSign, ansVarInterval];
			If[Length[ansVarInterval]==0, Throw[False,functionExit]];
			AppendTo[ansSatAtomList, atom];
			flag=1;
		];
	];
	If[flag==1,
		Throw[{True, ansVarInterval, ansSatAtomList, ansUnsatAtomList},functionExit],
		If[Length[ansClause]==0,
			Throw[{False, ansVarInterval, ansSatAtomList, ansUnsatAtomList},functionExit],
			Throw[{ansClause, ansVarInterval, ansSatAtomList, ansUnsatAtomList},functionExit];
		];
	];
,functionExit]];

InvPropLinearAtom[poly_, relaSign_, varList_, varInterval_]:=
Module[{i, coeffList, monoList, assignOne, ansInterval=Interval[{0,0}], coe, var, temp, ansLb, ansUb,functionExit=Unique["WolframLSExit"]},Catch[
	monoList=MonomialList[poly,varList];
	assignOne=Association[Table[varList[[j]]->1,{j,Length[varList]}]];
	coeffList=Table[monoList[[j]]/.assignOne,{j,Length[monoList]}];
	monoList=Table[monoList[[j]]/coeffList[[j]],{j,Length[monoList]}];
	i=1;
	While[i<=Length[coeffList],
		coe = coeffList[[i]];
		var = monoList[[i]];
		If[IntegerQ[var] && var==1,
			temp = Interval[{coe,coe}],
			temp = coe*varInterval[var];
		];
		ansInterval = temp+ansInterval;
		If[Min[ansInterval]==-Infinity && Max[ansInterval]==Infinity,
			Throw[2,functionExit];
		];
		i++;
	];
	ansLb = Min[ansInterval];
	ansUb = Max[ansInterval];
	If[ansLb!=ansUb,
		If[relaSign==1,
			If[ansLb>=0,
				Throw[1,functionExit],
				If[ansUb<=0,
					Throw[0,functionExit],
					Throw[2,functionExit];
				];
			],
			If[relaSign==-1,
				If[ansUb<=0,
					Throw[1,functionExit],
					If[ansLb>=0,
						Throw[0,functionExit],
						Throw[2,functionExit];
					];
				],
				If[ansLb<0 && ansUb>0,
					Throw[2,functionExit],
					Throw[0,functionExit];
				];
			];
		],
		If[relaSign!=0,
			If[ansLb*relaSign>0, Throw[1,functionExit],Throw[0,functionExit];],
			If[ansLb==0, Throw[1,functionExit], Throw[0,functionExit];];
		];
	];
,functionExit]];

OneVarLinearList[polyList_]:=
Module[{i, linearList={}, oneVarLinearList={}, poly, isLinear, isLinearOneVar,functionExit=Unique["WolframLSExit"]},Catch[
	i=1;
	While[i<=Length[polyList],
		poly = polyList[[i]];
		{isLinear, isLinearOneVar} = TestLinear[poly];
		If[isLinear,
			AppendTo[linearList, i];
			If[isLinearOneVar,
				AppendTo[oneVarLinearList, i];
			];
		];
		i++;
	];
	Throw[{linearList, oneVarLinearList},functionExit];
,functionExit]];

TestLinear[poly_]:=
Module[{varSet, deg, y,functionExit=Unique["WolframLSExit"]},Catch[
	varSet = Variables[poly];
	deg=Max[Exponent[(MonomialList[poly]/.Association[Map[#->y&,varSet]]),y]];
    If[deg==1,
        If[Length[varSet]==1,
            Throw[{True, True},functionExit],
            Throw[{True, False},functionExit];
        ],
        Throw[{False, False},functionExit];
    ];
,functionExit]];

SolveOneVarLinear[poly_, relaSign_, varInterval_]:=
Module[{var, c1, c0, inqValue, ans,functionExit=Unique["WolframLSExit"]},Catch[
	var = Variables[poly][[1]];
	c1 = Coefficient[poly, var, 1];
	c0 = Coefficient[poly, var, 0];
	inqValue = -c0/c1;
	If[relaSign*c1>0,
		ans = UpdateVarInterval[var,1,inqValue,varInterval];
		If[Length[ans]==0, Throw[False,functionExit], Throw[ans,functionExit]];
		,
		If[relaSign*c1<0,
			ans = UpdateVarInterval[var,-1,inqValue,varInterval];
			If[Length[ans]==0, Throw[False,functionExit], Throw[ans,functionExit]];
			,
			ans = UpdateVarInterval[var,0,inqValue,varInterval];
			If[Length[ans]==0, Throw[False,functionExit], Throw[ans,functionExit]];
		];
	];
,functionExit]];

UpdateVarInterval[var_, inqRela_, inqValue_, varInterval_]:=
Module[{varLb, varUb,functionExit=Unique["WolframLSExit"]},Catch[
	varLb = Min[varInterval[var]];
	varUb = Max[varInterval[var]];
	If[varLb==varUb,
		If[inqRela==1,
			If[varLb>inqValue,
				Throw[varInterval,functionExit],
				Throw[False,functionExit];
			],
			If[inqRela==-1,
				If[varLb<inqValue,
					Throw[varInterval,functionExit],
					Throw[False,functionExit];
				],
				If[varLb==inqValue,
					Throw[varInterval,functionExit],
					Throw[False,functionExit];
				];
			];
		],
		If[inqRela==1,
			If[inqValue<=varLb,
				Throw[varInterval,functionExit],
				If[varLb<inqValue && inqValue<varUb,
					Throw[UpValue[varInterval, var, Interval[{inqValue, varUb}]],functionExit],
					Throw[False,functionExit];
				];
			],
			If[inqRela==-1,
				If[inqValue>=varUb,
					Throw[varInterval,functionExit],
					If[varLb<inqValue && inqValue<varUb,
						Throw[UpValue[varInterval, var, Interval[{varLb, inqValue}]],functionExit]
					];
				],
				If[varLb<inqValue && inqValue<varUb,
					Throw[UpValue[varInterval, var, Interval[{inqValue, inqValue}]],functionExit],
					Throw[False,functionExit];
				];
			];
		];
	];
,functionExit]];

UpValue[x_, var_, varNewValue_]:=
Module[{tempx,functionExit=Unique["WolframLSExit"]},Catch[
	tempx = x;
	tempx[var] = varNewValue;
	Throw[tempx,functionExit];
,functionExit]];

IniMethodZero[varList_, varInterval_]:=
Module[{i, x=<||>, var, lb, ub, nume, deno,functionExit=Unique["WolframLSExit"]},Catch[
	i=0;
	While[i<=Length[varList]-1,
		i++;
		var = varList[[i]];
		lb = Min[varInterval[var]];
		ub = Max[varInterval[var]];
		If[Not[IntersectingQ[{lb,ub},{-Infinity,Infinity}]],
			If[lb!=ub,
				If[lb<1 && 1<ub,
					x[var] = 1,
					deno = RandomInteger[{2,100}];
				    nume = RandomInteger[{1,deno}];
					x[var] = lb+(ub-lb)*nume/deno;
				],
				x[var] = lb;
			],
			If[lb==-Infinity && ub==Infinity,
				x[var]=1,
				If[Not[IntersectingQ[{lb},{-Infinity,Infinity}]],
					If[lb<1,
						x[var] = 1,
						x[var] = lb + 1/2;
					],
					If[1<ub,
						x[var] = 1,
						x[var] = ub - 1/2;
					];
				];
			];
		];
	];
	Throw[x,functionExit];
,functionExit]];

IniMethodOne[varList_, varInterval_]:=
Module[{i, x=<||>, var, lb, ub, nume, deno,functionExit=Unique["WolframLSExit"]},Catch[
	i=1;
	While[i<=Length[varList],
		var = varList[[i]];
		lb = Min[varInterval[var]];
		ub = Max[varInterval[var]];
		If[Not[IntersectingQ[{lb,ub},{-Infinity,Infinity}]],
			If[lb!=ub,
				If[lb<-1 && 1<ub,
					x[var]=RandomChoice[{1,-1}],
					deno = RandomInteger[{2,100}];
				    nume = RandomInteger[{1,deno}];
					x[var] = lb+(ub-lb)*nume/deno;
				],
				x[var]=lb;
			],
			If[lb==-Infinity && ub==Infinity,
				x[var] = RandomChoice[{1,-1}],
				If[Not[IntersectingQ[{lb},{-Infinity,Infinity}]],
					If[lb<-1,
						x[var] = RandomChoice[{1,-1}],
						x[var] = lb+1/2;
					],
					If[1<ub,
						x[var] = RandomChoice[{1,-1}],
						x[var] = ub-1/2;
					];
				];
			];
		];
		i++;
	];
	Throw[x,functionExit];
,functionExit]];

IniMethodTwo[varList_, varInterval_]:=
Module[{i, x=<||>, var, lb, ub, nume, deno,functionExit=Unique["WolframLSExit"]},Catch[
	i=1;
	While[i<=Length[varList],
		var = varList[[i]];
		lb = Min[varInterval[var]];
		ub = Max[varInterval[var]];
		If[Not[IntersectingQ[{lb,ub},{-Infinity,Infinity}]],
			If[lb!=ub,
				deno = RandomInteger[{2,100}];
				nume = RandomInteger[{1,deno}];
			    x[var] = lb+(ub-lb)*nume/deno;
				,
				x[var]=lb;
			],
			If[lb==-Infinity && ub==Infinity,
				deno = RandomInteger[{2,100}];
				nume = RandomInteger[{1,deno}];
			    x[var] = -50+100*nume/deno;
			    ,
				If[Not[IntersectingQ[{lb},{-Infinity,Infinity}]],
					If[lb<50,
						deno = RandomInteger[{2,100}];
						nume = RandomInteger[{1,deno}];
			            x[var] = lb+(50-lb)*nume/deno;
						,
						x[var] = lb+1/2;
					],
					If[-50<ub,
						deno = RandomInteger[{2,100}];
						nume = RandomInteger[{1,deno}];
			            x[var] = -50+(ub+50)*nume/deno,
						x[var] = ub-1/2;
					];
				];
			];
		];
		i++;
	];
	Throw[x,functionExit];
,functionExit]];

LSSolver[polyList0_, cnf0_, varList_,lsLimit_,maxCntLS_]:=
Module[{cnt=1,init,lsInit={},ans,cons,consZero,polyList,cnf,LenDenNum,
		lnum,varnum,deg,
		linearList, oneVarLinearList, preproc, newPolyList, newCnf, newVarList, varInterval, varFixList,functionExit=Unique["WolframLSExit"]},Catch[
	cntLS=0;
    {linearList, oneVarLinearList} = OneVarLinearList[polyList0];
	preproc = LSPreproc[polyList0, cnf0, varList, linearList, oneVarLinearList];
	If[Length[preproc]==0,Throw[{"unknown","LS:preprocessing"},functionExit]];
	If[preproc[[1]]==False,
		newPolyList =preproc[[2]];
		newCnf = preproc[[3]];
		newVarList = preproc[[4]];
		varInterval = preproc[[5]];
		,
		Throw[{"sat","LSPreprocessing",preproc[[2]]},functionExit];
	];
	While[cnt<=lsLimit,
		Which[cnt==1,
			init=IniMethodZero[newVarList, varInterval];
			AppendTo[lsInit,init];
			ans=LS[init,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
            If[ans[[1]]!="unknown",Throw[ans,functionExit];];
			cnt++,
			cnt>=2&&cnt<=6,
			init=IniMethodOne[newVarList, varInterval];
			If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=LS[init,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
                If[ans[[1]]!="unknown",Throw[ans,functionExit];];
            ];
            cnt++,
            cnt>=7,
            init=IniMethodTwo[newVarList, varInterval];
            If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=LS[init,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
                If[ans[[1]]!="unknown",Throw[ans,functionExit];];
            ];
            cnt++;
		];
	];
	Throw[{"unknown","LS"},functionExit];
,functionExit]];

LSOriginal[x0_, polyList_, cnf_, varList_, varInterval_, maxCntLS_]:=
Module[{i, x, w, isAxis, x1, x2, isDir,
		cnt=1,init,lsInit={},varListLast,vars=Length[varList],varList2,
		clauses,y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum,varnum=Length[varList],functionExit=Unique["WolframLSExit"]},Catch[
	x = x0;$RestartCount++;$LastModel=x;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	While[True,
		$LastModel=x;
 If[SatCheck[polyList,cnf,varList,x] && FullModelQ[x],Throw[{"sat","LS",x},functionExit]];
		x1=x;
		If[cntLS>maxCntLS,Throw[{"unknown","LS:jump-budget",x},functionExit]];
        i=0;
		While[i<varnum,
			i++;
			If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>15,
				LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
				x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
		];
        cntLS++;
		{isAxis, x1} = SearchAndApplyOp1[polyList, cnf, varList, varInterval,  x, w];
		If[isAxis&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
            cntLS++;
			{isDir, x1} = GradSearchAndApplyOp1[polyList, cnf, varList, varInterval,  x, w];
			If[MemberQ[cycle,x1],Break[]];
			If[isDir&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
                cntLS++;
                Break[];
			];
		];
	];
	Throw[{"unknown","LS"},functionExit];
,functionExit]];

SamplePoint[polyList_,atomList_,assign_] := Module[{ans=<||>,poly,vars,key,samples,raw},
  If[!TrueQ[$Engineering],Return[RawSamplePoint[polyList,atomList,assign]]];
  Scan[Function[atom,
    poly=polyList[[atom[[1]]]]/.assign;vars=Variables[Simplify[poly]];
    If[vars==={},samples={},
      key={poly/.First[vars]->HoldComplete[LSUnivariate],"original-WL-root-samples"};
      If[TrueQ[PaperSolvers`Private`$CacheEnabled] && KeyExistsQ[$SampleCache,key],samples=$SampleCache[key],
        raw=RawSamplePoint[polyList,{atom},assign];samples=raw[atom];
        If[TrueQ[PaperSolvers`Private`$CacheEnabled] && Length[$SampleCache]<PaperSolvers`Private`$CacheLimit &&
          ListQ[samples] && AllTrue[samples,IntegerQ[#] || Head[#]===Rational&],$SampleCache[key]=samples]]];
    AssociateTo[ans,atom->samples]],atomList];ans
];
LS[x0_,p_,c_,v_,intervals_,limit_] := PaperSolvers`Private`WithSearchContext[p,c,v,pp,
  LSOriginal[x0,p,c,v,intervals,limit]];

End[];
EndPackage[];

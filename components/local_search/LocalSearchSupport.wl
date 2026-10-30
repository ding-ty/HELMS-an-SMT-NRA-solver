(* Exact preprocessing helpers for the shared local search driver.
   Bounds come exclusively from original unit clauses; the complete input
   formula must still be checked before reporting SAT. *)
BeginPackage["TwoDLSLocalSupport`"];
UnitLinearIntervals::usage = "UnitLinearIntervals[p,c,v] derives exact open rational intervals only from original unit affine clauses.";
OriginalStyleInitialAssignment::usage = "OriginalStyleInitialAssignment[v,intervals,round] gives an exact strict-interior assignment with the source initialization preferences.";
LineParameterInterval::usage = "LineParameterInterval[v,a,d,intervals] restricts t in a+t d to the known open bounds.";
IntervalLineSamples::usage = "IntervalLineSamples[q,sign,t,{lower,upper}] returns one rational sample per allowed open sector satisfying sign*q>0.";
NearestIntervalLineSamples::usage = "NearestIntervalLineSamples[q,sign,t,domain] returns the nearest of the generated allowed sector samples.";
SourceDirectionVectors::usage = "Exact gradient/current/random directions with source filtering.";
SourceDirectionFamily::usage = "Combined line directions and the original random subset for planar pairing.";
CompactRootInterval::usage = "Exact root enclosure with rational endpoint size controlled by the requested width.";
CompactRootIntervals::usage = "Disjoint enclosures for every distinct real root, refined exactly when needed.";
PolynomialSectorSamples::usage = "PolynomialSectorSamples[q,t,domain] returns an exact rational sample from every root-free open sector of a rational polynomial in the open rational domain.";
$SectorSamplePolicy::usage = "$SectorSamplePolicy selects one exact rational point per univariate sector: near-origin favors small moves; interior favors a midpoint for bounded sectors.";
$SectorSamplePolicy = "near-origin";
Begin["`Private`"];

(* Rational roots otherwise give singleton isolators that preserve every
   denominator bit. Grid brackets bound endpoint size without floating-point
   rounding. Existing callers still refine until neighboring roots separate. *)
CompactRootInterval[root_, width_] := If[
  (IntegerQ[root] || Head[root] === Rational) && TrueQ[width > 0],
  With[{denominator = Ceiling[1/width]},
    {Floor[denominator root]/denominator, Ceiling[denominator root]/denominator}],
  IsolatingInterval[root, width]];

CompactRootIntervals[roots_List, width_] := Module[
  {ordered = Sort[DeleteDuplicates[roots, TrueQ[#1 == #2] &], Less],
   currentWidth = width, intervals},
  intervals = CompactRootInterval[#, currentWidth] & /@ ordered;
  While[! And @@ Table[TrueQ[intervals[[i,2]] < intervals[[i+1,1]]],
      {i, Length[intervals]-1}],
    currentWidth /= 10;
    intervals = CompactRootInterval[#, currentWidth] & /@ ordered];
  intervals
];

RationalQ[x_] := IntegerQ[x] || Head[x] === Rational;
InsideQ[x_, {lo_, hi_}] := TrueQ[lo < x < hi];

UnitLinearIntervals[p_List, c_List, v_List] := Module[
  {bounds = AssociationThread[v, ConstantArray[{-Infinity, Infinity}, Length[v]]],
   used = {}, consistent = True, atom, q, involved, x, coefficient, constant, old, b},
  Do[
    If[clause === {}, consistent = False; Continue[]];
    If[Length[clause] =!= 1, Continue[]];
    atom = First[clause]; q = Expand[atom[[2]] p[[atom[[1]]]]];
    involved = Select[v, ! FreeQ[q, #] &];
    If[involved === {},
      If[RationalQ[q] && ! TrueQ[q > 0], consistent = False]; Continue[]];
    If[Length[involved] =!= 1, Continue[]];
    x = First[involved];
    If[! PolynomialQ[q, {x}] || Exponent[q, x] =!= 1, Continue[]];
    coefficient = Coefficient[q, x]; constant = q /. x -> 0;
    If[! RationalQ[coefficient] || ! RationalQ[constant] || coefficient === 0,
      Continue[]];
    b = -constant/coefficient; old = bounds[x];
    bounds[x] = If[TrueQ[coefficient > 0],
      {Max[old[[1]], b], old[[2]]}, {old[[1]], Min[old[[2]], b]}];
    AppendTo[used, atom];
    If[! TrueQ[bounds[x][[1]] < bounds[x][[2]]], consistent = False],
    {clause, c}];
  <|"intervals" -> bounds, "consistent" -> consistent,
    "used_atoms" -> DeleteDuplicates[used]|>
];

(* The open endpoints must never be sampled. In particular the numerator is
   strictly smaller than its denominator, correcting the endpoint draw in the
   historical initialization code. *)
InteriorFraction[] := Module[{denominator = RandomInteger[{2, 100}]},
  RandomInteger[{1, denominator - 1}]/denominator];

InitialCoordinate[{lo_, hi_}, round_Integer] := Module[{preferred},
  If[! TrueQ[lo < hi], Return[Missing["EmptyOpenInterval"]]];
  Which[
    round === 1,
      Which[InsideQ[1, {lo, hi}], 1,
        lo =!= -Infinity && hi =!= Infinity, (lo + hi)/2,
        lo =!= -Infinity, lo + 1/2, True, hi - 1/2],
    2 <= round <= 6,
      preferred = Select[{-1, 1}, InsideQ[#, {lo, hi}] &];
      Which[Length[preferred] === 2, RandomChoice[preferred],
        lo =!= -Infinity && hi =!= Infinity, lo + (hi - lo) InteriorFraction[],
        preferred =!= {}, First[preferred],
        lo =!= -Infinity, lo + 1/2, True, hi - 1/2],
    True,
      Which[lo =!= -Infinity && hi =!= Infinity, lo + (hi - lo) InteriorFraction[],
        lo === -Infinity && hi === Infinity, -50 + 100 InteriorFraction[],
        lo =!= -Infinity, If[TrueQ[lo < 50], lo + (50 - lo) InteriorFraction[], lo + 1/2],
        True, If[TrueQ[-50 < hi], -50 + (hi + 50) InteriorFraction[], hi - 1/2]]]
];

OriginalStyleInitialAssignment[v_List, intervals_Association, round_Integer] :=
  AssociationThread[v, (InitialCoordinate[intervals[#], round] &) /@ v];

LineParameterInterval[v_List, a_Association, d_List, intervals_Association] := Module[
  {lo = -Infinity, hi = Infinity, bound, current, direction, local, inconsistent = False},
  If[Length[v] =!= Length[d], Return[Missing["DirectionDimension"]]];
  Do[
    bound = intervals[v[[i]]]; current = a[v[[i]]]; direction = d[[i]];
    If[TrueQ[direction == 0],
      If[! InsideQ[current, bound], inconsistent = True; Break[]],
      local = If[TrueQ[direction > 0],
        {(bound[[1]] - current)/direction, (bound[[2]] - current)/direction},
        {(bound[[2]] - current)/direction, (bound[[1]] - current)/direction}];
      lo = Max[lo, local[[1]]]; hi = Min[hi, local[[2]]]],
    {i, Length[v]}];
  If[! inconsistent && TrueQ[lo < hi], {lo, hi}, Missing["EmptyOpenInterval"]]
];

RationalInterior[lo_, hi_] := Module[{denominator = 1, value},
  If[! TrueQ[lo < hi], Return[Missing["EmptyOpenInterval"]]];
  If[InsideQ[0, {lo, hi}], Return[0]];
  If[lo === -Infinity, Return[Floor[hi] - 1]];
  If[hi === Infinity, Return[Ceiling[lo] + 1]];
  While[True,
    value = (Floor[denominator lo] + 1)/denominator;
    If[InsideQ[value, {lo, hi}], Return[value]];
    denominator *= 10]
];

(* Work with primitive integer polynomials throughout root isolation.  In
   Mathematica 14, constructing exact Root objects and then comparing or
   isolating those objects can terminate the kernel on rational polynomials
   with very large coefficients.  RootIntervals accepts the integer polynomial
   directly and returns ordered rational brackets.  No approximate root or
   floating-point sign test is used here. *)
PrimitiveIntegerPolynomial[q_, t_] := Module[{coefficients, denominator, content},
  If[q === 0, Return[0]];
  If[! PolynomialQ[q, {t}], Return[$Failed]];
  coefficients = CoefficientList[q, t];
  If[coefficients === {}, Return[0]];
  If[! And @@ (RationalQ /@ coefficients), Return[$Failed]];
  denominator = LCM @@ (Denominator /@ coefficients);
  coefficients *= denominator;
  content = GCD @@ coefficients;
  If[content === 0, Return[0]];
  Expand[FromDigits[Reverse[coefficients/content], t]]
];

(* Every non-singleton RootIntervals bracket contains exactly one root in
   its interior.  Its endpoint can be a different rational root, so use the
   one-sided sign of the square-free polynomial at that endpoint. *)
RefinePolynomialBracket[p_, dp_, t_, {lo_, hi_}] := Module[{middle, left, value},
  If[lo === hi, Return[{lo, hi}]];
  middle = (lo + hi)/2; value = p /. t -> middle;
  If[value === 0, Return[{middle, middle}]];
  left = p /. t -> lo;
  If[left === 0, left = dp /. t -> lo];
  If[Sign[left] === Sign[value], {middle, hi}, {lo, middle}]
];

(* Minimize displacement along the search line within each cell.  A midpoint
   of an entire bounded cell may unnecessarily leave constraints that were
   already satisfied.  The point below stays strictly inside the cell and
   close to the boundary on the side of the current assignment t == 0.
   Choose a short decimal rational in that safe window rather than adding a
   constant to an endpoint with a potentially enormous denominator. *)
NearOriginSectorSample[lo_, hi_] := Module[{step = 1/10000},
  If[! TrueQ[lo < hi], Return[Missing["EmptyOpenInterval"]]];
  If[InsideQ[0, {lo, hi}], Return[0]];
  If[lo =!= -Infinity && hi =!= Infinity, step = Min[step, (hi - lo)/4]];
  If[TrueQ[lo >= 0], RationalInterior[lo, lo + step],
    -RationalInterior[-hi, -hi + step]]
];

(* A second, deterministic representative gives restart rounds a different
   jump scale.  Both policies sample exactly one point per open sector and
   retain the same exact root isolation and final sign checks. *)
SectorSample[lo_, hi_] := If[$SectorSamplePolicy === "interior",
  Which[
    ! TrueQ[lo < hi], Missing["EmptyOpenInterval"],
    lo === -Infinity && hi === Infinity, 1,
    lo === -Infinity || hi === Infinity, NearOriginSectorSample[lo, hi],
    True, (lo + hi)/2],
  NearOriginSectorSample[lo, hi]
];

PolynomialSectorSamples[q_, t_, domain_ : {-Infinity, Infinity}] := Module[
  {poly = Expand[q], lo, hi, primitive, squarefree, derivative, isolated,
   brackets, selected = {}, bracket, discard, currentWidth, denominator,
   compact, samples, left, right, i},
  If[! MatchQ[domain, {_, _}], Return[{}]];
  {lo, hi} = domain;
  If[! (lo === -Infinity || RationalQ[lo]) ||
      ! (hi === Infinity || RationalQ[hi]) || ! TrueQ[lo < hi], Return[{}]];
  primitive = PrimitiveIntegerPolynomial[poly, t];
  If[primitive === $Failed || primitive === 0, Return[{}]];
  If[FreeQ[primitive, t], Return[{SectorSample[lo, hi]}]];
  squarefree = PrimitiveIntegerPolynomial[
    PolynomialQuotient[primitive, PolynomialGCD[primitive, D[primitive, t]], t], t];
  derivative = D[squarefree, t];
  isolated = Quiet[RootIntervals[squarefree]];
  If[! MatchQ[isolated, {_List, _List}], Return[{}]];
  brackets = First[isolated];
  If[! And @@ (MatchQ[#, {_?RationalQ, _?RationalQ}] &&
      TrueQ[#[[1]] <= #[[2]]] & /@ brackets), Return[{}]];
  (* Resolve domain membership using only rational comparisons.  A root on
     an open domain endpoint is excluded rather than treated as a sector. *)
  Do[
    bracket = original; discard = False;
    If[TrueQ[bracket[[2]] <= lo] || TrueQ[hi <= bracket[[1]]], Continue[]];
    While[lo =!= -Infinity && TrueQ[bracket[[1]] <= lo < bracket[[2]]],
      If[TrueQ[bracket[[1]] < lo] && (squarefree /. t -> lo) === 0,
        discard = True; Break[]];
      bracket = RefinePolynomialBracket[squarefree, derivative, t, bracket]];
    If[discard || TrueQ[bracket[[2]] <= lo], Continue[]];
    While[hi =!= Infinity && TrueQ[bracket[[1]] < hi <= bracket[[2]]],
      If[TrueQ[hi < bracket[[2]]] && (squarefree /. t -> hi) === 0,
        discard = True; Break[]];
      bracket = RefinePolynomialBracket[squarefree, derivative, t, bracket]];
    If[discard || TrueQ[hi <= bracket[[1]]], Continue[]];
    AppendTo[selected, bracket], {original, brackets}];
  If[selected === {}, Return[{SectorSample[lo, hi]}]];
  (* RootIntervals can use shared endpoints for adjacent open brackets.
     Refine until there is an explicitly rational gap between every pair. *)
  Do[
    While[! TrueQ[selected[[i, 2]] < selected[[i + 1, 1]]],
      selected[[i]] = RefinePolynomialBracket[squarefree, derivative, t, selected[[i]]];
      selected[[i + 1]] = RefinePolynomialBracket[squarefree, derivative, t, selected[[i + 1]]]],
    {i, Length[selected] - 1}];
  currentWidth = 1/10000;
  While[True,
    Do[While[TrueQ[selected[[i, 2]] - selected[[i, 1]] > currentWidth],
      selected[[i]] = RefinePolynomialBracket[squarefree, derivative, t, selected[[i]]]],
      {i, Length[selected]}];
    denominator = Ceiling[1/currentWidth];
    compact = ({Floor[denominator #[[1]]]/denominator,
      Ceiling[denominator #[[2]]]/denominator} &) /@ selected;
    If[TrueQ[lo < compact[[1, 1]]] && TrueQ[compact[[-1, 2]] < hi] &&
      And @@ Table[TrueQ[compact[[i, 2]] < compact[[i + 1, 1]]],
      {i, Length[compact] - 1}], Break[]];
    currentWidth /= 10];
  samples = Table[
    left = If[i === 1, lo, compact[[i - 1, 2]]];
    right = If[i > Length[compact], hi, compact[[i, 1]]];
    SectorSample[left, right], {i, Length[compact] + 1}];
  Select[DeleteDuplicates[samples], RationalQ[#] && InsideQ[#, domain] &&
    (poly /. t -> #) =!= 0 &]
];
PolynomialSectorSamples[___] := {};

IntervalLineSamples[q_, sign_, t_, {lo_, hi_}] := Module[
  {poly = Expand[q], samples},
  samples = PolynomialSectorSamples[poly, t, {lo, hi}];
  Select[samples, TrueQ[sign (poly /. t -> #) > 0] &]
];
IntervalLineSamples[___] := {};
NearestIntervalLineSamples[q_, sign_, t_, domain_] := Module[
  {samples = IntervalLineSamples[q, sign, t, domain]},
  If[samples === {}, {}, MinimalBy[samples, Abs]]
];

(* Audit-only production-ready helper. No file in the distributed solver is
   modified by loading this file. Input coefficients and assignment values are
   exact; no N, floating-point normalization or angular tolerance is used.
   This preserves the original source's Union ordering and first surviving
   representative of each one-dimensional span. *)
DirectionVectorsFromRandom[p_List, v_List, a_Association, randomVectors_List] :=
 Module[{gradients, current, directions, n=Length[v], positions, pivot},
  If[n==0,Return[{}]];
  gradients=Table[(D[p[[i]],#]& /@ v)/.Normal[a],{i,Length[p]}];
  current=Lookup[a,v];
  directions=Union[gradients,{current},
    randomVectors];
  directions=Select[directions,!And@@(TrueQ[#==0]& /@ #)&];
  positions=Select[Range[Length[directions]],Function[k,
    pivot=SelectFirst[Range[n],!TrueQ[directions[[k,#]]==0]&];
    AnyTrue[Take[directions,k-1],
      TrueQ[(#[[pivot]]/directions[[k,pivot]]) directions[[k]] == #]&]]];
  Delete[directions,List /@ positions]
 ];

SourceDirectionVectors[p_List, v_List, a_Association, randomCount_Integer:10] :=
  DirectionVectorsFromRandom[p, v, a, Table[RandomInteger[{-1000,1000},Length[v]],{randomCount}]];
SourceDirectionFamily[p_List, v_List, a_Association, randomCount_Integer] := Module[{random},
  random = Table[RandomInteger[{-1000,1000},Length[v]],{randomCount}];
  <|"all" -> DirectionVectorsFromRandom[p, v, a, random], "random" -> random|>
];

End[];
EndPackage[];

(*  Mathematica Logic package.
    Copyright (C) 2019  José María Cruz Lorite

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/
*)

BeginPackage["Logic`"];

(* Enable overriding built-in TautologyQ *)
Unprotect[TautologyQ];
ClearAll[TautologyQ];

(* Set HoldAll *)
SetAttributes[{HeadlessTruthTable, TruthTable, ContradictionQ, TautologyQ,
	DisjunctiveForm, ConjunctiveForm, UnpackSequence}, HoldAll];

TruthTable::usage = "TruthTable[expr, {v1, v2, ..., vn}] computes the truth table for any combination of truth values of {v1, v2, ..., vn}.
TruthTable[expr] is the inmediate version of TruthTable[expr, {v1, v2, ..., vn}]. If any variable returned by BooleanVariables[expr] has a defined value, the function will fail.";

HeadlessTruthTable::usage = "HeadlessTruthTable[expr, {v1, v2, ..., vn}] computes the truth table for any combination of truth values of {v1, v2, ..., vn} but without header row.
HeadlessTruthTable[expr] is the inmediate verion of HeadlessTruthTable[expr, {v1, v2, ..., vn}]. If any variable returned by BooleanVariables[expr] has a defined value, the function will fail.";

TautologyQ::usage = "TautologyQ[expr, {v1, v2, ..., vn}] return True if expr is a tautology for any combination of truth values of {v1, v2, ..., vn}.
TautologyQ[expr] is the inmediate verion of TautologyQ[expr, {v1, v2, ..., vn}]. If any variable returned by BooleanVariables[expr] has a defined value, the function will fail.";

ContradictionQ::usage = "ContradcitionQ[expr, {v1, v2, ..., vn}] return True if expr is a contradiction for any combination of truth values of {v1, v2, ..., vn}.
ContradictionQ[expr] is the inmediate verion of ContradictionQ[expr, {v1, v2, ..., vn}]. If any variable returned by BooleanVariables[expr] has a defined value, the function will fail.";

DisjunctiveForm::usage ="DisjunctiveForm[expr] gives the normal disjunctive form of expr. If any variable returned by BooleanVariables[expr] has a defined value, the function will fail.";

ConjunctiveForm::usage = "ConjunctiveForm[expr] gives the normal conjunctive form of expr. If any variable returned by BooleanVariables[expr] has a defined value, the function will fail.";

(* Private namespace *)
Begin["`Private`"];

(* Headless TruthTable for only one variable expressions. (Recursion stop) *)
HeadlessTruthTable[exp_, {v_Symbol}]:=Block[{v},
	{{True, exp/.{v->True}}, {False, exp/.{v->False}}}
];

(* Headless TruthTable for multiple variable expressions. (Divide and conquer) *)
HeadlessTruthTable[expr_, {v_Symbol, vars__Symbol}]:=Block[{vars, v},
	Join[(Prepend[#, True])&/@HeadlessTruthTable[expr/.{v->True}, {vars}],
		 (Prepend[#, False])&/@HeadlessTruthTable[expr/.{v->False}, {vars}]]];
		 
(* HeadlessTruthTable with heading *)
TruthTable[expr_, {vars__Symbol}]:=Block[{vars},
	TableForm[HeadlessTruthTable[expr, {vars}],
	TableHeadings->{None, Append[UnpackSequence[{vars}], HoldForm[expr]]}]
];

(* Disjunctive normal form *)
DisjunctiveForm[expr_]:=Block[{trues, table, conjunctions, vars},
	vars = BooleanVariables[expr];
	table = HeadlessTruthTable[expr];
	(* Check fails *)
	If[table==$Failed, Message[DisjunctiveForm::exprerror, vars, expr]; Return[$Failed]];
	(* Get True rows, then remove last column *)
	trues = Most/@Select[table, Last[#]&];
	conjunctions = Apply[And][Partition[Riffle[vars, #], 2]/.{{x_, True}->x, {x_, False}->!x}]&/@trues;
	Apply[Or][conjunctions]
];

(* Conjunctive normal form *)
ConjunctiveForm[expr_]:=Block[{falses, table, disjunctions, vars},
	vars = BooleanVariables[expr];
	table = HeadlessTruthTable[expr];
	(* Check fails *)
	If[table==$Failed, Message[ConjunctiveForm::exprerror, vars, expr]; Return[$Failed]];
	(* Get false rows, then remove last column *)
	falses = Most/@Select[table, !Last[#]&];
	disjunctions = Apply[Or][Partition[Riffle[vars, #], 2]/.{{x_, True}->!x, {x_, False}->x}]&/@falses;
	Apply[And][disjunctions]
];

(* Tautology test *)
TautologyQ[expr_, {vars__Symbol}]:=Block[{table},
	table = Last/@HeadlessTruthTable[expr, {vars}];
	(*  Check that all values are booleans *)
	If[!AllTrue[table, BooleanQ], Message[TautologyQ::exprerror, expr, {vars}]; Return[$Failed]];
	And@@table
];

(* Contradiction test *)
ContradictionQ[expr_, {vars__Symbol}]:=Block[{table},
	table = Last/@HeadlessTruthTable[expr, {vars}];
	(*  Check that all values are booleans *)
	If[!AllTrue[table, BooleanQ], Message[ContradictionQ::exprerror, expr, {vars}]; Return[$Failed]];
	!Or@@table
];
	
(* Inmediate version *)
HeadlessTruthTable[expr_]:=HeadlessTruthTable[expr, Evaluate[{Sequence@@BooleanVariables[expr]}]];
TruthTable[expr_]:=TruthTable[expr, Evaluate[{Sequence@@BooleanVariables[expr]}]];
TautologyQ[expr_]:=TautologyQ[expr, Evaluate[{Sequence@@BooleanVariables[expr]}]];
ContradictionQ[expr_]:=ContradictionQ[expr, Evaluate[{Sequence@@BooleanVariables[expr]}]];

(* Return a list with all received symbols unevaluated *)
(* Used to construct table heading on TruthTable function *)
UnpackSequence[{v_}] := {HoldForm[v]};
UnpackSequence[{v_, vars__}] := Join[{HoldForm[v]}, UnpackSequence[{vars}]];

(* Wrong arguments received *)
HeadlessTruthTable::argserror = "Type mismatch HeadlessTruthTable[`1`]. See HeadlessTruthTable::usage for more help.";
TruthTable::argserror = "Type mismatch TruthTable[`1`]. See TruthTable::usage for more help.";
ContradictionQ::argserror = "Type mismatch ContradictionQ[`1`]. See ContradictionQ::usage for more help.";
ContradictionQ::exprerror = "The expression '`1`' evaluated for `2` gives not Boolean results.";
TautologyQ::argserror = "Type mismatch TautologyQ[`1`]. See TautologyQ::usage for more help.";
TautologyQ::exprerror = "The expression '`1`' evaluated for `2` gives not Boolean results.";
DisjunctiveForm::exprerror = "Not all variables `1` on expression '`2`' are Symbols.";
DisjunctiveForm::argserror = "Type mismatch DisjunctiveForm[`1`]. See DisjunctiveForm::usage for more help.";
ConjunctiveForm::exprerror = "Not all variables `1` on expression '`2`' are Symbols.";
ConjunctiveForm::argserror = "Type mismatch ConjunctiveForm[`1`]. See ConjunctiveForm::usage for more help.";

HeadlessTruthTable[args___] := (Message[HeadlessTruthTable::argserror, {args}];$Failed);
TruthTable[args___] := (Message[TruthTable::argserror, {args}];$Failed);
ContradictionQ[args___] := (Message[ContradictionQ::argserror, {args}]; $Failed);
TautologyQ[args___] := (Message[TautologyQ::argserror, {args}];$Failed);
DisjunctiveForm[args___] := (Message[DisjunctiveForm::argserror, {args}];$Failed);
ConjunctiveForm[args___] := (Message[ConjunctiveForm::argserror, {args}];$Failed);

End[];
EndPackage[];

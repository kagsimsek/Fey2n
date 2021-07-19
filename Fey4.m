(*** Fey2n ***)
(*** v0.1.1 ***)
(*** K$, 7/2021 ***)

Run["clear"]

Print["Fey2n: Feynman rules for dimension-2n SM(EFT)"]
Print["by K. Simsek, 7/2021\n"]

Print["[Note: Only the case n = 2 is available at the moment.]\n"]

START = SessionTime[]

(* coding aliases *)

ClearAll[CU, $I]

CU = $I

$I /: $I^n_ := (-1)^(-n) $I^(-n) /; n < 0
$I /: $I^n_ := $I $I^(n-1) /; n > 2
$I /: $I^2 = -1

ClearAll[TOE, TOS]

TOE[x_] := ToExpression[x]
TOS[x_] := ToString[x]

(* mathematical objects *)

ClearAll[tau0, tau1, tau2, tau3, taup, taum, g, \[Delta], \[Delta]SU3, Vud]

tau0 = DiagonalMatrix[{1,1}]
tau1 = {
  {0, 1},
  {1, 0}
}
tau2 = {
  {0, -CU},
  {CU, 0}
}
tau3 = DiagonalMatrix[{1, -1}]

taup = (tau1 + CU tau2) / 2
taum = (tau1 - CU tau2) / 2

Attributes[g] = {Orderless}
Attributes[\[Delta]] = {Orderless}
Attributes[\[Delta]SU3] = {Orderless};

Vud /: Conjugate[Vud[i_, j_]] Vud[j_, k_] := \[Delta][i, k]

(* parameters *)

Print["Setting up parameters..."]

NumberGen = 3

Mup[1] = Mu
Mup[2] = Mc
Mup[3] = Mt
Mdo[1] = Md
Mdo[2] = Ms
Mdo[3] = Mb
Mel[1] = Me
Mel[2] = Mmu
Mel[3] = Mtau

Parameters = {
  G1, G2, G3, EE,
  MW, MZ, Mh,
  Mup /@ Range[NumberGen], Mdo /@ Range[NumberGen], Mel /@ Range[NumberGen],
  Mup[_], Mdo[_], Mel[_],
  CW, SW,
  VEV,
  Xi
} // Flatten

(* fields *)

Print["Setting up fields..."]

ClearAll[VectorFields, ScalarFields, FermionFields]

VectorFields = {
  Wp[mu_] :> {anti Wm[mu] + mass MW},
  Wm[mu_] :> {anti Wp[mu] + mass MW},
  Z[mu_] :> {anti Z[mu] + mass MZ},
  A[mu_] :> {anti A[mu]}
}

ScalarFields = {
  h -> {anti h + mass Mh},
  phip -> {anti phim + mass Xi MW},
  phim -> {anti phip + mass Xi MW},
  phiZ -> {anti phiZ + mass Xi MZ}
}

FermionFields = {
  up[f_] :> {anti bar[up[f]] + mass Mup[f]},
  down[f_] :> {anti bar[down[f]] + mass Mdo[f]},
  electron[f_] :> {anti bar[electron[f]] + mass Mel[f]},
  nu[f_] :> {anti bar[nu[f]]}
}

(* assumptions *)

$Assumptions = {
  CW^2 + SW^2 == 1,
  MW > 0, MZ > 0, Mh > 0,
  Mup[#] > 0 & /@ Range[NumberGen],
  Mdo[#] > 0 & /@ Range[NumberGen],
  Mel[#] > 0 & /@ Range[NumberGen],
  G3 > 0, G2 > 0, G1 > 0, EE > 0,
  Xi > 0
} // Flatten

(* check_if operators *)

ClearAll[NotFieldQ, ParamQ, ScalarsQ, VectorsQ, FermionsQ]

NotFieldQ[x_ + y_] := NotFieldQ[x] + NotFieldQ[y]
NotFieldQ[x_ y_] := NotFieldQ[x] NotFieldQ[y]
NotFieldQ[x_] := !ContainsAny[
  {x, Head @ x, First @ x, Head @ First @ x},
  Join[
    Head /@ VectorFields[[All, 1]],
    ScalarFields[[All, 1]],
    Head /@ FermionFields[[All, 1]]
  ]
] // Quiet
ParamQ[x_] := MemberQ[Parameters, x]
ScalarsQ[x_] := MemberQ[ScalarFields[[All, 1]], x]
VectorsQ[x_] := ContainsAny[
  {x, Head @ x},
  Head /@ VectorFields[[All, 1]]
]
FermionsQ[P[x_, mu_]] := False
FermionsQ[x_] := ContainsAny[
  {x, Head @ x, Head @ First @ x},
  Head /@ FermionFields[[All, 1]]
] // Quiet

(* physical objects *)

ClearAll[ECharge, LeptonNumber, QuarkNumber]

ECharge[a_ + b_] := ECharge[a] + ECharge[b]
ECharge[a_ b_] := ECharge[a] ECharge[b]
ECharge[x_?ArrayQ] := Module[
  {arr, i},
  arr = {};
  For[i = 1, i <= Length[x], i++,
    arr = Append[arr, ECharge[x[[i]]]]
  ];
  Return[arr]
]
ECharge[a_?NumericQ] := 0
ECharge[a_?NotFieldQ] := 0

LeptonNumber[a_ + b_] := LeptonNumber[a] + LeptonNumber[b]
LeptonNumber[a_ b_] := LeptonNumber[a] LeptonNumber[b]
LeptonNumber[x_?ArrayQ] := Module[
  {arr, i},
  arr = {};
  For[i = 1, i <= Length[x], i++,
    arr = Append[arr, LeptonNumber[x[[i]]]]
  ];
  Return[arr]
]
LeptonNumber[a_?NumericQ] := 0
LeptonNumber[a_?NotFieldQ] := 0

QuarkNumber[a_ + b_] := QuarkNumber[a] + QuarkNumber[b]
QuarkNumber[a_ b_] := QuarkNumber[a] QuarkNumber[b]
QuarkNumber[x_?ArrayQ] := Module[
  {arr, i},
  arr = {};
  For[i = 1, i <= Length[x], i++,
    arr = Append[arr, QuarkNumber[x[[i]]]]
  ];
  Return[arr]
]
QuarkNumber[a_?NumericQ] := 0
QuarkNumber[a_?NotFieldQ] := 0

(* derivative operator *)

ClearAll[Deriv]

Deriv[a_?ArrayQ, mu_] := Module[
  {arr, i},
  arr = {};
  For[i = 1, i <= Length[a], i++,
    arr = Append[arr, Deriv[a[[i]], mu]]
  ];
  Return[arr]
]
Deriv[a_ + b_, mu_] := Deriv[a, mu] + Deriv[b, mu]
Deriv[a_ b_, mu_] := Deriv[a, mu] b + a Deriv[b, mu]
Deriv[-a_, mu_] := -Deriv[a, mu]
Deriv[a_?NumericQ, mu_] := 0
Deriv[a_?ParamQ, mu_] := 0
Deriv[a_?NotFieldQ, mu_] := 0
Deriv[$I, mu_] := 0
Deriv /: Deriv[x_, mu_] := -CU P[x, mu] x

(* adjoint operator *)

ClearAll[Adjoint]

Adjoint[x_?ArrayQ] := Module[
  {arr, i},
  arr = {};
  For[i = 1, i <= Length[x], i++,
    arr = Append[arr, Adjoint[x[[i]]]]
  ];
  Return[arr]
]
Adjoint[a_ + b_] := Adjoint[a] + Adjoint[b]
Adjoint[a_ b_] := Adjoint[a] Adjoint[b]
Adjoint[-a_] := -Adjoint[a]
Adjoint[x_^n_] := Adjoint[x]^n
Adjoint[a_?ParamQ] := a
Adjoint[a_?NumericQ] := a
Adjoint[CU] = -CU
Adjoint[Mel[f_]] := Mel[f]
Adjoint[Mup[f_]] := Mup[f]
Adjoint[Mdo[f_]] := Mdo[f]
Adjoint[g[mu_, nu_]] := g[mu, nu]
Adjoint[\[Delta][f1_, f2_]] := \[Delta][f1, f2]
Adjoint[\[Delta]SU3[f1_, f2_]] := \[Delta]SU3[f1, f2]
Adjoint[bar[F_]] := F
Adjoint[P[x_, mu_]] := -P[Adjoint[x], mu]
Adjoint[Vud[f1_, f2_]] := Conjugate[Vud[f2, f1]]
Adjoint[Conjugate[Vud[f2_, f1_]]] := Vud[f1, f2]
Adjoint[x_?ScalarsQ] := Coefficient[First[x /. ScalarFields], anti]
Adjoint[x_?VectorsQ] := Coefficient[First[x /. VectorFields], anti]
Adjoint[x_?FermionsQ] := Coefficient[First[x /. FermionFields], anti]
Adjoint[DiracChain[args___]] := Module[
  {lst, rlst, nlst, i},
  lst = {args};
  rlst = Reverse[lst];
  nlst = {};
  For[i = 1, i <= Length[lst], i++,
    nlst = Append[nlst, Adjoint[rlst[[i]]]]
  ];
  Return[DiracChain @@ nlst]
]
Adjoint[DiracG[mu_]] := DiracG[mu]
Adjoint[DiracG5] = -DiracG5
Adjoint[PL] = PR
Adjoint[PR] = PL

(* dirac chain *)

ClearAll[DiracOperators, DiracOperatorQ, NotDiracOperatorQ, NotFermionsQ, NotDiracQ, DiracChain];

DiracOperators = {
  PR, PL, DiracG, DiracG5, DiracS
}

DiracOperatorQ[a_ + b_] := DiracOperatorQ[a] + DiracOperatorQ[b]
DiracOperatorQ[a_ b_] := DiracOperatorQ[a] DiracOperatorQ[b]
DiracOperatorQ[x_] := If[
  ContainsAny[{x, Head @ x}, DiracOperators],
  True,
  False
] // Quiet

NotDiracOperatorQ[x_] := !DiracOperatorQ[x]

NotFermionsQ[a_ + b_] := NotFermionsQ[a] + NotFermionsQ[b]
NotFermionsQ[a_ b_] := NotFermionsQ[a] NotFermionsQ[b]
NotFermionsQ[x_] := !FermionsQ[x]

NotDiracQ[x_] := NotFermionsQ[x] && NotDiracOperatorQ[x]

DiracChain[L___, PR, PL, R___] := 0
DiracChain[L___, PL, PR, R___] := 0
DiracChain[L___, PR, PR, R___] := DiracChain[L, PR, R] // ExpandAll
DiracChain[L___, PL, PL, R___] := DiracChain[L, PL, R] // ExpandAll
DiracChain[L___, PR, DiracG[mu_], R___] := DiracChain[L, DiracG[mu], PL, R] // ExpandAll
DiracChain[L___, PL, DiracG[mu_], R___] := DiracChain[L, DiracG[mu], PR, R] // ExpandAll
DiracChain[L___, PR, DiracS[mu_, nu_], R___] := DiracChain[L, DiracS[mu, nu], PL, R] // ExpandAll
DiracChain[L___, PL, DiracS[mu_, nu_], R___] := DiracChain[L, DiracG[mu, nu], PR, R] // ExpandAll
DiracChain[f1_?ArrayQ, M___, f2_?ArrayQ] := Sum[
  DiracChain[f1[[i]], M, f2[[i]]],
  {i, 1, Length[f1]}
] // Expand // ExpandAll
DiracChain[L___, a_ + b_, R___] := DiracChain[L, a, R] + DiracChain[L, b, R] // ExpandAll
DiracChain[L___, a_?NumericQ b_, R___] := a DiracChain[L, b, R] // ExpandAll
DiracChain[L___, -a_, R___] := -DiracChain[L, a, R] // ExpandAll
DiracChain[L___, a_?NotDiracQ b_, R___] := a DiracChain[L, b, R] // ExpandAll
DiracChain /: DiracChain[PL] + DiracChain[PR] = 1
DiracChain /: DiracChain[L___, PL, R___] + DiracChain[L___, PR, R___] := DiracChain[L, R]
DiracChain /: -DiracChain[PL] + DiracChain[PR] := DiracChain[DiracG5]
DiracChain /: DiracChain[PL] - DiracChain[PR] := -DiracChain[DiracG5]
DiracChain /: -DiracChain[L___, PL, R___] + DiracChain[L___, PR, R___] := DiracChain[L, DiracG5, R]
DiracChain /: DiracChain[L___, PL, R___] - DiracChain[L___, PR, R___] := -DiracChain[L, DiracG5, R]

(* vertex selector *)

ClearAll[FieldDer]

FieldDer[a_ + b_, A_] := FieldDer[a, A] + FieldDer[b, A]
FieldDer[a_ b_, A_] := FieldDer[a, A] b + a FieldDer[b, A]
FieldDer[a_?ParamQ, A_] := 0
FieldDer[a_?NumericQ, A_] := 0
FieldDer[a_, A_?ScalarsQ] := D[a, A]
FieldDer[DiracChain[L___, F2_[f2_]], F_?FermionsQ[f_]] := \[Delta][f, f2] DiracChain[L] /; F === F2
FieldDer[DiracChain[bar[F1_[f1_]], R___], bar[F_[f_]]] := \[Delta][f, f1] DiracChain[R] /; F === F1
FieldDer[A1_[mu_], A2_?VectorsQ[nu_]] := g[mu, nu] /; A1 === A2
FieldDer[G[a1_, mu1_], G[a2_, mu2_]] := \[Delta]SU3[a1, a2] g[mu1, mu2]
FieldDer[a_, A_] := 0 /; FreeQ[a, A] || FreeQ[a, Head @ A]

ClearAll[MuIndices, fIndices, ffIndices, Contract]

MuIndices = TOE["mu" <> TOS[#]] & /@ Range[10]
fIndices = TOE["f" <> TOS[#]] & /@ Range[10]
ffIndices = TOE["f" <> TOS[#] <> "f" <> TOS[#]] & /@ Range[10]

Contract[expr_] := Module[
  {dum},
  dum[1] = expr // Expand;
  dum[2] = dum[1] //. g[a_, b_] fac_ :> ReplaceAll[b -> a][fac] /; (!FreeQ[fac, b]) && (MemberQ[MuIndices, a] || MemberQ[MuIndices, b]);
  dum[3] = dum[2] //. \[Delta][fi1_, fi2_] fac_ :> ReplaceAll[fi2 -> fi1][fac] /; !FreeQ[fac, fi2] && (MemberQ[Join[fIndices, ffIndices], fi1] || MemberQ[Join[fIndices, ffIndices], fi2]);
  Return[dum[3] // FullSimplify]
]

ClearAll[Vertex]

Vertex[lst_] := Module[
  {dum, i},
  dum[1] = Lagrangian;
  For[i = 1, i <= Length[lst], i++,
   dum[1] = FieldDer[dum[1], lst[[i]]]
  ];
  dum[2] = dum[1] /. Derivative[n_, mu_][P][F_, nu_] :> 0;
  dum[3] = dum[2] /. P[F_, mu_] :> P[TOS[F], mu];
  dum[4] = dum[3] /. ((VectorFields[[All, 1]][[#]] :> 0 &) /@ Range[Length[VectorFields[[All, 1]]]]);
  dum[5] = dum[4] /. ((ScalarFields[[All, 1]][[#]] -> 0 &) /@ Range[Length[ScalarFields[[All, 1]]]]);
  dum[6] = dum[5] /. P[F_, mu_] :> P[TOE[F], mu];
  dum[7] = dum[6] /. $I -> I;
  Return[I dum[7] // Contract]
]
Vertex[lst_, Lag_] := Module[
  {dum, i},
  dum[1] = Lag;
  For[i = 1, i <= Length[lst], i++,
   dum[1] = FieldDer[dum[1], lst[[i]]]
  ];
  dum[2] = dum[1] /. Derivative[n_, mu_][P][F_, nu_] :> 0;
  dum[3] = dum[2] /. P[F_, mu_] :> P[TOS[F], mu];
  dum[4] = dum[3] /. ((VectorFields[[All, 1]][[#]] :> 0 &) /@ Range[Length[VectorFields[[All, 1]]]]);
  dum[5] = dum[4] /. ((ScalarFields[[All, 1]][[#]] -> 0 &) /@ Range[Length[ScalarFields[[All, 1]]]]);
  dum[6] = dum[5] /. P[F_, mu_] :> P[TOE[F], mu];
  dum[7] = dum[6] /. $I -> I;
  Return[I dum[7] // Contract]
]

(* gauge sector *)

Print["Setting up the gauge sector..."]

ECharge[A[mu_]] := 0
ECharge[Z[mu_]] := 0
ECharge[Wp[mu_]] := 1
ECharge[Wm[mu_]] := -1

LeviCivita3[1, 2, 3] = 1
LeviCivita3[L___, j_, i_, R___] := -LeviCivita3[L, i, j, R] /; i < j
LeviCivita3[L___, i_, j_, R___] := 0 /; i == j

W1[mu_] := (Wp[mu] + Wm[mu]) / Sqrt[2]
W2[mu_] := CU (Wm[mu] - Wp[mu]) / Sqrt[2]
W3[mu_] := Z[mu] CW - A[mu] SW
B[mu_] := Z[mu] SW + A[mu] CW

FieldStrengthG[a_, b_, c_, mu_, nu_] := Deriv[G[a, mu], nu] -
  Deriv[G[a, nu], mu] +
  G3 fSU3[a, b, c] G[b, mu] G[c, nu]
FieldStrengthW[i_, mu_, nu_] := Deriv[TOE["W" <> TOS[i]][mu], nu] -
  Deriv[TOE["W" <> TOS[i]][nu], mu] +
  G2 Sum[
    LeviCivita3[i, j, k] TOE["W" <> TOS[j]][mu] TOE["W" <> TOS[k]][nu],
    {j, 1, 3}, {k, 1, 3}
  ]
FieldStrengthB[mu_, nu_] := Deriv[B[mu], nu] - Deriv[B[nu], mu]

GaugaFixingG = Deriv[G[a1, mu1], mu2] g[mu1, mu2] Deriv[G[a2, mu3], mu4] g[mu3, mu4] \[Delta]SU3[a1, a2]
GaugeFixingA = Deriv[A[mu1], mu2] g[mu1, mu2] Deriv[A[mu3], mu4] g[mu3, mu4]
GaugeFixingZ = (Deriv[Z[mu1], mu2] g[mu1, mu2] - Xi MZ phiZ) (Deriv[Z[mu3], mu4] g[mu3, mu4] - Xi MZ phiZ)
GaugeFixingW = (Deriv[Wp[mu1], mu2] g[mu1, mu2] - CU Xi MW phip) (Deriv[Wm[mu3], mu4] g[mu3, mu4] + CU Xi MW phim)

LagG = - 1 / 4 Sum[
    FieldStrengthW[i, mu1, mu2] FieldStrengthW[i, mu3, mu4] g[mu1, mu3] g[mu2, mu4],
    {i, 1, 3}
  ] -
  1 / 4 FieldStrengthB[mu1, mu2] FieldStrengthB[mu3, mu4] g[mu1, mu3] g[mu2, mu4] -
  1 / 2 / Xi GaugeFixingA -
  1 / 2 / Xi GaugeFixingZ -
  1 / Xi GaugeFixingW

(* higgs sector *)

Print["Setting up the Higgs sector..."]

ECharge[phip] = 1
ECharge[phim] = -1
ECharge[h] = 0
ECharge[phiZ] = 0

HiggsMu = Mu / Sqrt[2]
HiggsLam = HiggsMu^2 / VEV^2

Phi = {
  phip,
  (VEV + h + CU phiZ) / Sqrt[2]
}

CovariantD[Phi, mu_] := Deriv[Phi, mu] -
  CU G2 / Sqrt[2] (taup Wp[mu] + taum Wm[mu]) . Phi +
  CU EE ECharge[Phi] A[mu] tau0 . Phi -
  CU G2 / CW Z[mu] (1 / 2 tau3 - ECharge[Phi] SW^2 tau0) . Phi

LagH = Adjoint[CovariantD[Phi, mu1]] . CovariantD[Phi, mu2] g[mu1, mu2] +
  HiggsMu^2 Adjoint[Phi] . Phi -
  HiggsLam (Adjoint[Phi] . Phi)^2

(* fermion sector *)

Print["Setting up the fermion sector..."]

ECharge[electron[f_]] := -1
ECharge[nu[f_]] := 0
ECharge[up[f_]] := 2 / 3
ECharge[down[f_]] := - 1 / 3
ECharge[bar[F_]] := -ECharge[F]

LeptonNumber[electron[f_]] := 1
LeptonNumber[nu[f_]] := 1
LeptonNumber[bar[F_]] := -LeptonNumber[F]
LeptonNumber[x_] := 0

QuarkNumber[up[f_]] := 1
QuarkNumber[down[f_]] := 1
QuarkNumber[bar[F_]] := -QuarkNumber[F]
QuarkNumber[x_] := 0

ClearAll[LL, QL, ER, UR, DR]

LL[f_] := {nu[f], electron[f]}
QL[f_] := {up[f], down[f]}
ER[f_] := electron[f]
UR[f_] := up[f]
DR[f_] := down[f]

ClearAll[CKM]

CKM[QL[f_]] := {
  up[f],
  Vud[f, TOE[TOS[f] <> TOS[f]]] down[TOE[TOS[f] <> TOS[f]]]
}

CovariantD[LL[f_], mu_] := Deriv[LL[f], mu] -
  CU G2 / Sqrt[2] (taup Wp[mu] + taum Wm[mu]) . LL[f] +
  CU EE ECharge[LL[f]] A[mu] tau0 . LL[f] -
  CU G2 / CW (1 / 2 tau3 - ECharge[LL[f]] SW^2 tau0) . LL[f] Z[mu]
CovariantD[QL[f_], mu_] := Deriv[CKM[QL[f]], mu] -
  CU G2 / Sqrt[2] (taup Wp[mu] + taum Wm[mu]) . CKM[QL[f]] +
  CU EE ECharge[QL[f]] A[mu] tau0 . CKM[QL[f]] -
  CU G2 / CW (1 / 2 tau3 - ECharge[LL[f]] SW^2 tau0) . CKM[QL[f]] Z[mu]
CovariantD[ER[f_], mu_] := Deriv[ER[f], mu] +
  CU EE ECharge[ER[f]] A[mu] ER[f] +
  CU G2 / CW ECharge[ER[f]] SW^2 Z[mu] ER[f]
CovariantD[UR[f_], mu_] := Deriv[UR[f], mu] +
  CU EE ECharge[UR[f]] A[mu] UR[f] +
  CU G2 / CW ECharge[UR[f]] SW^2 Z[mu] UR[f]
CovariantD[DR[f_], mu_] := Deriv[DR[f], mu] +
  CU EE ECharge[DR[f]] A[mu] DR[f] +
  CU G2 / CW ECharge[DR[f]] SW^2 Z[mu] DR[f]

LagF = DiracChain[Adjoint[LL[f1]], CU DiracG[mu2], PL, CovariantD[LL[f2], mu1]] \[Delta][f1, f2] g[mu1, mu2] +
  DiracChain[Adjoint[CKM[QL[f1]]], CU DiracG[mu2], PL, CovariantD[QL[f2], mu1]] \[Delta][f1, f2] g[mu1, mu2] +
  DiracChain[Adjoint[ER[f1]], CU DiracG[mu2], PR, CovariantD[ER[f2], mu1]] \[Delta][f1, f2] g[mu1, mu2] +
  DiracChain[Adjoint[UR[f1]], CU DiracG[mu2], PR, CovariantD[UR[f2], mu1]] \[Delta][f1, f2] g[mu1, mu2] +
  DiracChain[Adjoint[DR[f1]], CU DiracG[mu2], PR, CovariantD[DR[f2], mu1]] \[Delta][f1, f2] g[mu1, mu2] // ExpandAll

(* yukawa sector *)

Print["Setting up the Yukawa sector..."]

TildePhi = CU tau2 . Adjoint[Phi]

yL = Me / VEV Sqrt[2]
yU = Mu / VEV Sqrt[2]
yD = Md / VEV Sqrt[2]

LagY = -yL DiracChain[Adjoint[LL[f1]] . Phi, PR, ER[f2]] \[Delta][f1, f2] -
  yD DiracChain[Adjoint[CKM[QL[f1]]] . Phi, PR, Vud[f2, f2f2] DR[f2f2]] \[Delta][f1, f2] -
  yU DiracChain[Adjoint[CKM[QL[f1]]] . TildePhi, PR, UR[f2]] \[Delta][f1, f2] // ExpandAll
LagY = LagY + Adjoint[LagY] // ExpandAll

(* lagrangian *)

Print["Setting up the Lagrangian..."]

Lagrangian = LagG + LagH + LagF + LagY

(* prettify *)

ClearAll[Prettify]

Prettify = {
  A[mu_] :> Subscript[A, mu],
  Z[mu_] :> Subscript[Z, mu],
  Wp[mu_] :> Subsuperscript[W, mu, "+"],
  Wm[mu_] :> Subsuperscript[W, mu, "-"],
  phip -> Superscript[\[Phi], "+"],
  phim -> Superscript[\[Phi], "-"],
  phiZ -> Subscript[\[Phi], Z],
  G1 -> Subscript[g, 1],
  G2 -> Subscript[g, 2],
  G3 -> Subscript[g, 3],
  EE -> e,
  MW -> Subscript[m, W],
  MZ -> Subscript[m, Z],
  Mh -> Subscript[m, h],
  CW -> Cos[Subscript[\[Theta], W]],
  SW -> Sin[Subscript[\[Theta], W]],
  VEV -> v,
  Xi -> \[Xi],
  g[\[Mu]_, \[Nu]_] :> Subscript[g, \[Mu], \[Nu]],
  \[Delta][f1_, f2_] :> Subscript[\[Delta], f1, f2],
  P[a_, \[Mu]_] :> Subsuperscript[p, \[Mu], a],
  DiracChain[DQ___] :> If[Length[{DQ}] > 1, NonCommutativeMultiply[DQ], DQ],
  PL -> Subscript[P, L],
  PR -> Subscript[P, R],
  Dirac1 -> 1,
  DiracG[mu_] :> Subscript[\[Gamma], mu],
  DiracG5 -> Subscript[\[Gamma], 5],
  DiracS[mu_, nu_] :> Subscript[\[Sigma], mu, nu],
  F1 -> Subscript[f, 1],
  F2 -> Subscript[f, 2],
  F3 -> Subscript[f, 3],
  F4 -> Subscript[f, 4],
  Me -> Subscript[m, e],
  Mu -> Subscript[m, u],
  Md -> Subscript[m, d],
  Mel[f_] :> Subscript[m, e, f],
  Mup[f_] :> Subscript[m, u, f],
  Mdo[f_] :> Subscript[m, d, f],
  Vud[f1_, f2_] :> Subscript[V, f1, f2],
  Conjugate[Vud[f1_, f2_]] :> Superscript[Subscript[V, f1, f2], "*"],
  bar[electron[f_]] :> Subscript[OverBar[e], f],
  bar[nu[f_]] :> Subscript[OverBar[\[Nu]], f],
  bar[up[f_]] :> Subscript[OverBar[u], f],
  bar[down[f_]] :> Subscript[OverBar[d], f],
  electron[f_] :> Subscript[e, f],
  nu[f_] :> Subscript[\[Nu], f],
  up[f_] :> Subscript[u, f],
  down[f_] :> Subscript[d, f]
}

(* all vertices *)

Print["Setting up the vertices..."]

AllScalars = ScalarFields[[All, 1]]
AllVectors = Head /@ VectorFields[[All, 1]]
AllFermions = Head /@ FermionFields[[All, 1]]

NeutralQ[x_?ArrayQ] := If[
  Total @ ECharge[x] == 0 && Total @ LeptonNumber[x] == 0 && Total @ QuarkNumber[x] == 0,
  True,
  False
]

ClearAll[SSSSVertices]
SSSSVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = i, j <= Length[AllScalars], j++,
   For[k = j, k <= Length[AllScalars], k++,
    For[l = k, l <= Length[AllScalars], l++,
     vrt = {AllScalars[[i]], AllScalars[[j]], AllScalars[[k]], AllScalars[[l]]};
     SSSSVertices = Append[SSSSVertices, vrt];
     ]
    ]
   ]
  ]
Clear[i, j, k, l, vrt]
SSSSVertices = Select[SSSSVertices, NeutralQ[#] &]

ClearAll[SSSVertices]
SSSVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = i, j <= Length[AllScalars], j++,
   For[k = j, k <= Length[AllScalars], k++,
    vrt = {AllScalars[[i]], AllScalars[[j]], AllScalars[[k]]};
    SSSVertices = Append[SSSVertices, vrt];
    ]
   ]
  ]
Clear[i, j, k, vrt]
SSSVertices = Select[SSSVertices, NeutralQ[#] &]

ClearAll[VVVVVertices]
VVVVVertices = {}
For[i = 1, i <= Length[AllVectors], i++,
  For[j = i, j <= Length[AllVectors], j++,
   For[k = j, k <= Length[AllVectors], k++,
    For[l = k, l <= Length[AllVectors], l++,
     vrt = {AllVectors[[i]][\[Mu]], AllVectors[[j]][\[Nu]], AllVectors[[k]][\[Alpha]], AllVectors[[l]][\[Beta]]};
     VVVVVertices = Append[VVVVVertices, vrt];
     ]
    ]
   ]
  ]
Clear[i, j, k, l, vrt]
VVVVVertices = Select[VVVVVertices, NeutralQ[#] &]

ClearAll[SVVVVertices]
SVVVVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = 1, j <= Length[AllVectors], j++,
   For[k = j, k <= Length[AllVectors], k++,
    For[l = k, l <= Length[AllVectors], l++,
     vrt = {AllScalars[[i]], AllVectors[[j]][\[Mu]], AllVectors[[k]][\[Alpha]], AllVectors[[l]][\[Beta]]};
     SVVVVertices = Append[SVVVVertices, vrt];
     ]
    ]
   ]
  ]
Clear[i, j, k, l, vrt]
SVVVVertices = Select[SVVVVertices, NeutralQ[#] &]

ClearAll[SSVVVertices]
SSVVVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = i, j <= Length[AllScalars], j++,
   For[k = 1, k <= Length[AllVectors], k++,
    For[l = k, l <= Length[AllVectors], l++,
     vrt = {AllScalars[[i]], AllScalars[[j]], AllVectors[[k]][\[Mu]], AllVectors[[l]][\[Nu]]};
     SSVVVertices = Append[SSVVVertices, vrt];
     ]
    ]
   ]
  ]
Clear[i, j, k, l, vrt]
SSVVVertices = Select[SSVVVertices, NeutralQ[#] &]

ClearAll[SSSVVertices]
SSSVVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = i, j <= Length[AllScalars], j++,
   For[k = j, k <= Length[AllScalars], k++,
    For[l = 1, l <= Length[AllVectors], l++,
     vrt = {AllScalars[[i]], AllScalars[[j]], AllScalars[[k]], AllVectors[[l]][\[Mu]]};
     SSSVVertices = Append[SSSVVertices, vrt];
     ]
    ]
   ]
  ]
Clear[i, j, k, l, vrt]
SSSVVertices = Select[SSSVVertices, NeutralQ[#] &]

ClearAll[VVVVertices]
VVVVertices = {}
For[i = 1, i <= Length[AllVectors], i++,
  For[j = i, j <= Length[AllVectors], j++,
   For[k = j, k <= Length[AllVectors], k++,
    vrt = {AllVectors[[i]][\[Mu]], AllVectors[[j]][\[Alpha]], AllVectors[[k]][\[Beta]]};
    VVVVertices = Append[VVVVertices, vrt];
    ]
   ]
  ];
Clear[i, j, k, l, vrt]
VVVVertices = Select[VVVVertices, NeutralQ[#] &]

ClearAll[SVVVertices]
SVVVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = 1, j <= Length[AllVectors], j++,
   For[k = j, k <= Length[AllVectors], k++,
    vrt = {AllScalars[[i]], AllVectors[[j]][\[Mu]], AllVectors[[k]][\[Nu]]};
    SVVVertices = Append[SVVVertices, vrt];
    ]
   ]
  ];
Clear[i, j, k, l, vrt]
SVVVertices = Select[SVVVertices, NeutralQ[#] &]

ClearAll[SSVVertices]
SSVVertices = {}
For[i = 1, i <= Length[AllScalars], i++,
  For[j = i, j <= Length[AllScalars], j++,
   For[k = 1, k <= Length[AllVectors], k++,
    vrt = {AllScalars[[i]], AllScalars[[j]], AllVectors[[k]][\[Mu]]};
    SSVVertices = Append[SSVVertices, vrt];
    ]
   ]
  ];
Clear[i, j, k, l, vrt]
SSVVertices = Select[SSVVertices, NeutralQ[#] &]

ClearAll[FFSVertices]
FFSVertices = {}
For[i = 1, i <= Length[AllFermions], i++,
  For[j = 1, j <= Length[AllFermions], j++,
   For[k = 1, k <= Length[AllScalars], k++,
    vrt = {bar[AllFermions[[j]][F2]], AllFermions[[i]][F1], AllScalars[[k]]};
    FFSVertices = Append[FFSVertices, vrt];
    ]
   ]
  ];
Clear[i, j, k, l, vrt]
FFSVertices = Select[FFSVertices, NeutralQ[#] &]

ClearAll[FFVVertices]
FFVVertices = {}
For[i = 1, i <= Length[AllFermions], i++,
  For[j = 1, j <= Length[AllFermions], j++,
   For[k = 1, k <= Length[AllVectors], k++,
    vrt = {bar[AllFermions[[j]][F2]], AllFermions[[i]][F1], AllVectors[[k]][\[Mu]]};
    FFVVertices = Append[FFVVertices, vrt];
    ]
   ]
  ];
Clear[i, j, k, l, vrt]
FFVVertices = Select[FFVVertices, NeutralQ[#] &]

AllVertices = Join[
   VVVVVertices, SVVVVertices, SSVVVertices, SSSVVertices,
   SSSSVertices,
   VVVVertices, SVVVertices, SSVVertices, SSSVertices,
   FFSVertices, FFVVertices
   ]

Print["Deriving the vertex factors..."]

Vertices = Vertex /@ AllVertices

Print["Tabulating the results..."]

VerticesGrid = Table[
  {
    k,
    AllVertices[[k]] //. Prettify,
    Vertices[[k]] //. Prettify
  },
  {k, 1, Length[Vertices]}
];

VerticesTeX = (Grid@Select[VerticesGrid, !MemberQ[#, 0] &]) // TeXForm

(* export *)

Print["Exporting the results..."]

Dir = DirectoryName @ $InputFileName
OutputFile = Dir <> "fromMathematica.txt"
TeXFile = Dir <> "Fey4.tex"
PDFFile = Dir <> "Fey4.pdf"
Run["rm " <> PDFFile <> " 2>/dev/null"]
Run["rm " <> OutputFile <> " 2>/dev/null"]
Run["rm " <> TeXFile <> " 2>/dev/null"]
Export[OutputFile, {VerticesTeX}]
Run["file=" <> OutputFile <> " && \\
sed -i 's/\\\\begin{array}{ccc}//g' $file && \\
sed -i 's/\\\\end{array}//g' $file && \\
sed -i 's/\\\\text{\\*\\*}/ /g' $file && \\
sed -i 's/{}\\^\\*/\\^\\*/g' $file && \\
sed -i 's/,//g' $file && \\
sed -i 's/\\\\left\\\\{//g' $file && \\
sed -i 's/\\\\right\\\\}//g' $file && \\
sed -i 's/\\\\{//g' $file && \\
sed -i 's/\\\\}//g' $file"]
Run["echo '\\documentclass{article}' > " <> TeXFile]
Run["echo '\\usepackage[margin=1cm,letterpaper]{geometry}' >> " <> TeXFile]
Run["echo '\\usepackage{array,longtable}' >> " <> TeXFile]
Run["echo '\\newcolumntype{C}{>{$}c<{$}}' >> " <> TeXFile]
Run["echo '\\newcolumntype{L}{>{$}l<{$}}' >> " <> TeXFile]
Run["echo '\\setlength\\tabcolsep{5pt}' >> " <> TeXFile]
Run["echo '\\pagenumbering{gobble}' >> " <> TeXFile]
Run["echo '\\begin{document}' >> " <> TeXFile]
Run["echo '\\begin{center}' >> " <> TeXFile]
Run["echo 'K\\c{S} \\hfill \\sc Fey4 \\hfill \\today' >> " <> TeXFile]
Run["echo '\\end{center}' >> " <> TeXFile]
Run["echo '{\\renewcommand{\\arraystretch}{1.5}\\begin{longtable}{|C|C|L|}' >> " <> TeXFile]
Run["echo '\\hline' >> " <> TeXFile]
Run["echo '\\input{fromMathematica.txt}' >> " <> TeXFile]
Run["echo '\\hline' >> " <> TeXFile]
Run["echo '\\end{longtable}}' >> " <> TeXFile]
Run["echo 'All the momenta are assumed into the vertex.' >> " <> TeXFile]
Run["echo 'Derivatives have been replaces by $ -ip $.' >> " <> TeXFile]
Run["echo 'The sign convention of Advanced QFT by Romao have been used.' >> " <> TeXFile]
Run["echo 'Vertices contain the overall $ i $ factor.' >> " <> TeXFile]
Run["echo '\\end{document}' >> " <> TeXFile]

Print["Running pdflatex..."]
Run["cd " <> Dir <> " && pdflatex -shell-escape -interaction=nonstopmode Fey4.tex > /dev/null"]

Print["Cleaning up the room..."]
Run["rm " <> Dir <> "Fey4.aux" <> " 2>/dev/null"]
Run["rm " <> Dir <> "Fey4.log" <> " 2>/dev/null"]
Run["rm " <> Dir <> "Fey4.synctex.gz" <> " 2>/dev/null"]
Run["rm " <> TeXFile <> " 2>/dev/null"]
Run["rm " <> OutputFile <> " 2>/dev/null"]

Hourize[x_] := Module[
  {hr, min, sec},
  hr = Floor[x / 3600];
  min = Floor[(x - 3600 hr) / 60];
  sec = Round[Mod[x - 3600 hr - 60 min, 3600]];
  Return[{hr, min, sec}]
]

END = SessionTime[]
DUR = END - START
HRS = Hourize[DUR][[1]]
MINS = Hourize[DUR][[2]]
SECS = Hourize[DUR][[3]]

Print["\nRun time = ", HRS, ":", MINS, ":", SECS]

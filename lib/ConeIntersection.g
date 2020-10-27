#
#
# We need function for computing the intersection V cap C
# but we need to do it without computing facets of Perf(eG) [Very expensive and useless]
# Full dimension of the space is D.
# So if we have the equations
# lambda_1 v1 + ... lambda_N vN = mu_1 w1 + .... + mu_M wM
# with mu_i >= 0 and lambda_j in R.
# We can rexpress as f_k(mu_1, ...., mu_M) = 0 for some linear function f_k
# Number of such equations is D - N.
# So, if we have m parameters then the dimension of the space of possible parameters
# is M - (D-N).
# 
# Find a number of mu_i as parameter and express other from them.
# such as mu_k = phi_k(mu_i1, ..., mu_ip)
# The inequalities becomes phi_k(....) >= 0
# [ The reduction is done as AX = -BY ]
#  
# 
CONEINT_GetFundamentalObject:=function(BasisSpann, EXT)
  local nbEXT, NSP, nbEqua, TheFullMat, iEXT, iEqua, eScal, eSelect, nbSel, ListVar, nbVar, TheFullMatRed, iSel, TheFullMatPart, iVar, MappingFunction, FAC, eProd;
  nbEXT:=Length(EXT);
  NSP:=NullspaceMat(TransposedMat(BasisSpann));
  nbEqua:=Length(NSP);
  TheFullMat:=NullMat(nbEqua, nbEXT);
  for iEXT in [1..nbEXT]
  do
    for iEqua in [1..nbEqua]
    do
      eScal:=NSP[iEqua] * EXT[iEXT];
      TheFullMat[iEqua][iEXT]:=eScal;
    od;
  od;
  eSelect:=ColumnReduction(TheFullMat).Select;
  nbSel:=Length(eSelect);
  ListVar:=Difference([1..nbEXT], eSelect);
  nbVar:=Length(ListVar);
  TheFullMatRed:=NullMat(nbEqua, nbSel);
  for iSel in [1..nbSel]
  do
    iEXT:=eSelect[iSel];
    for iEqua in [1..nbEqua]
    do
      TheFullMatRed[iEqua][iSel]:=TheFullMat[iEqua][iEXT];
    od;
  od;
  TheFullMatPart:=NullMat(nbEqua, nbVar);
  for iVar in [1..nbVar]
  do
    iEXT:=ListVar[iVar];
    for iEqua in [1..nbEqua]
    do
      TheFullMatPart[iEqua][iVar]:=-TheFullMat[iEqua][iEXT];
    od;
  od;
  #
  FAC:=[];
  Append(FAC, IdentityMat(nbVar));
  eProd:=Inverse(TheFullMatRed) * TheFullMatPart;
  Append(FAC, eProd);
  #
  MappingFunction:=function(eVectEXT)
    local eVect, iVar, iEXT, iSel, eLine, eScal, eSolFull, eSol;
    if Length(eVectEXT)<>nbVar then
      Error("Wrong length on input");
    fi;
    eVect:=ListWithIdenticalEntries(nbEXT, 0);
    for iVar in [1..nbVar]
    do
      iEXT:=ListVar[iVar];
      eVect[iEXT]:=eVectEXT[iVar];
    od;
    for iSel in [1..nbSel]
    do
      iEXT:=eSelect[iSel];
      eLine:=eProd[iSel];
      eScal:=eLine * eVectEXT;
      eVect[iEXT]:=eScal;
    od;
    eSolFull:=TransposedMat(EXT) * eVect;
    eSol:=SolutionMat(BasisSpann, eSolFull);
    return eSol;
  end;
  return rec(FAC:=FAC, NSP:=NSP, eSelect:=eSelect, MappingFunction:=MappingFunction);
end;

#
# The rationale of this function is that it allows to compute
# whether the cone intersection    V inter C    is full dimensional in V.
#
CONEINT_FindSpaceIntersection:=function(BasisSpann, EXT)
  local TheRec, LinSpace, TheSpaceSpann;
  TheRec:=CONEINT_GetFundamentalObject(BasisSpann, EXT);
  #
  LinSpace:=LinearDeterminedByInequalities(TheRec.FAC);
  TheSpaceSpann:=List(LinSpace, TheRec.MappingFunction);
  #
  return RowReduction(TheSpaceSpann).EXT;
end;

CONEINT_FindInteriorPoint:=function(BasisSpann, EXT)
  local TheRec, n, ListAddEqua, MatrixFaceStab, eInterior, eSol;
  TheRec:=CONEINT_GetFundamentalObject(BasisSpann, EXT);
  n:=Length(TheRec.FAC[1]);
  ListAddEqua:=[];
  MatrixFaceStab:=Group([IdentityMat(n)]);
  eInterior:=GetSpaceInteriorPoint(ListAddEqua, TheRec.FAC, MatrixFaceStab, "simplelp");
  eSol:=TheRec.MappingFunction(eInterior);
  return eSol;
end;



CONEINT_ComputeStabilizerOfIntersection:=function(BasisSpann, EXT)
  local n, Qmat, eEXT, Qinv, BasisProd, BasisOrth, FullBasis, OrthogonalProjection, i, eVect, eSol, eVectProj, j, nbEXT, ScalarMat, iEXT, eLine, jEXT, eScal1, eScal2, eEnt, PermGRP, ListMatrGensSubspace, eGen, eMatrFull, eMatrSub, eBasis, eBasisImg, GRPsubspace;
  n:=Length(EXT[1]);
  Qmat:=NullMat(n,n);
  for eEXT in EXT
  do
    Qmat:=Qmat + TransposedMat([eEXT]) * [eEXT];
  od;
  Qinv:=Inverse(Qmat);
  BasisProd:=BasisSpann * Qinv;
  BasisOrth:=NullspaceMat(TransposedMat(BasisProd));
  FullBasis:=Concatenation(BasisSpann, BasisOrth);
  OrthogonalProjection:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    eSol:=SolutionMat(FullBasis, eVect);
    eVectProj:=ListWithIdenticalEntries(n,0);
    for j in [1..Length(BasisSpann)]
    do
      eVectProj:=eVectProj + eSol[j] * BasisSpann[j];
    od;
    Add(OrthogonalProjection, eVectProj);
  od;
  nbEXT:=Length(EXT);
  ScalarMat:=[];
  for iEXT in [1..nbEXT]
  do
    eLine:=[];
    for jEXT in [1..nbEXT]
    do
      eScal1:=EXT[iEXT] * Qinv * EXT[jEXT];
#      eScal2:=EXT[iEXT] * (Qinv * OrthogonalProjection) * EXT[jEXT];
      eScal2:=EXT[iEXT] * (OrthogonalProjection * Qinv) * EXT[jEXT];
      eEnt:=[eScal1, eScal2];
      Add(eLine, eEnt);
    od;
    Add(ScalarMat, eLine);
  od;
  PermGRP:=AutomorphismWeightedDigraph(ScalarMat);
  ListMatrGensSubspace:=[];
  for eGen in GeneratorsOfGroup(PermGRP)
  do
    eMatrFull:=FindTransformation(EXT, EXT, eGen);
    eMatrSub:=[];
    for eBasis in BasisSpann
    do
      eBasisImg:=eBasis * eMatrFull;
      eSol:=SolutionMat(BasisSpann, eBasisImg);
      Add(eMatrSub, eSol);
    od;
    Add(ListMatrGensSubspace, eMatrSub);
  od;
  GRPsubspace:=Group(ListMatrGensSubspace);
  return rec(GRPsubspace:=GRPsubspace);
end;


# Apply a non-clever algorithm for computing the intersection
# Useful for debugging
CONEINT_ComputeIntersectionDirectly:=function(BasisSpann, EXT)
  local FAC, DimSpace, ListIneq, eFAC, eIneq, EXTint, FACint;
  FAC:=DualDescription(EXT);
  DimSpace:=Length(BasisSpann);
  ListIneq:=[];
  for eFAC in FAC
  do
    eIneq:=List(BasisSpann, x->x*eFAC);
    if eIneq<>ListWithIdenticalEntries(DimSpace, 0) then
      Add(ListIneq, eIneq);
    fi;
  od;
  EXTint:=DualDescription(ListIneq);
  FACint:=DualDescription(EXTint);
  return rec(EXT:=EXTint, FAC:=FACint);
end;




#
# We have a cone C determined by spanning set of rays (w1, ...., wN)
# We want to compute the interesection D = C \cap V for a subspace V spanned by
# v1, ...., vD
# W is moderately dimensional and we want to avoid at all costs the computation
# of a dual description of C which is very expensive.
# But is is fine to have a double description of D
# The equation set that we have is
#        sum lambda_i v_i = sum_j mu_j w_j with lambda_i in R and mu_j >= 0.
# We denote by v'_i the basis of the orthogonal space to V.
#
# Tools:
# ---What we first need to do is compute the group of symmetries of C that also
#    preserve the subspace W.
# ---Another tool is ability to check if a point x is in D via linear programming.
#    If it is not in D. We can 
# ---Another tool that we have is the space of equations
#    sum mu_j <w_j , v'_i> = 0 with mu_j >= 0.
#    We can minimize a function f(x) on V. This allow to check if an inequality
#    is a fcet and if not find a violated vertex.
#
# We can to the following:
# ---We can compute an initial list of vertices.
# ---We get the facets of this list by dual description
# ---We check if the facets are really facet and compute by optimization
#    New vertices if needed.
# ---Terminate when everything is done.
# ---Use symmetries all along the way.
CONEINT_ComputeDoubleDescriptionIntersection:=function(BasisSpann, EXT)
  local DimSpace, RecGRP, TotRec, IsPointInCone, FacetCheck, ListEqua, eNSP, eEqua, eEXT, eScal, ListIneq, ListEquaTot, BasisLin, eBvect, eSolPoint, TheCompl, TheComplBasisSpann, eCompl, ListIneqPoly, eIneq, eIneqPoly, InequalityComputation, nbEXT, eRecFAC, EXTint, ComputeInitialList, GetPermGRPvert, GRPext, LOrbFAC, IsComplete, eO, eIncd, FuncInsertEXT, eFAC, eComplEXT, eComplSpace, eRepr, EXTsave;
  DimSpace:=Length(BasisSpann);
  nbEXT:=Length(EXT);
  RecGRP:=CONEINT_ComputeStabilizerOfIntersection(BasisSpann, EXT);
  Print("|GRPsubspace|=", Order(RecGRP.GRPsubspace), " |BasisSpann|=", Length(BasisSpann), " |EXT|=", Length(EXT), "\n");
  TotRec:=CONEINT_GetFundamentalObject(BasisSpann, EXT);
  IsPointInCone:=function(eVect)
    local eVectFull, eSol;
    eVectFull:=eVect*TransposedMat(BasisSpann);
    eSol:=SolutionMatNonnegative(EXT, eVectFull);
    if eSol=fail then
      return false;
    fi;
    return true;
  end;
  # Linear programming to do is
  # sum_i mu_i w_i = x = sum_j lambda_j v_j
  # with mu_i >= 0.
  # The dimension of the linear program is nbEXT
  # We express the problem as a polytope by having
  # sum_i mu_i = 1
  ListEqua:=[];
  for eNSP in TotRec.NSP
  do
    eEqua:=[];
    for eEXT in EXT
    do
      eScal:=eEXT * eNSP;
      Add(eEqua, eScal);
    od;
    Add(ListEqua, eEqua);
  od;
  ListIneq:=IdentityMat(nbEXT);
  #
  ListEquaTot:=Concatenation(ListEqua, [ListWithIdenticalEntries(nbEXT, 1)]);
  BasisLin:=NullspaceMat(TransposedMat(ListEquaTot));
  eBvect:=Concatenation(ListWithIdenticalEntries(Length(TotRec.NSP),0), [1]);
  eSolPoint:=SolutionMat(TransposedMat(ListEquaTot), eBvect);
  TheCompl:=Concatenation([eSolPoint], BasisLin);
  TheComplBasisSpann:=[];
  for eComplEXT in TheCompl
  do
    eComplSpace:=eComplEXT * EXT;
    Add(TheComplBasisSpann, SolutionMat(BasisSpann, eComplSpace));
  od;
  #
  ListIneqPoly:=[];
  for eIneq in ListIneq
  do
    eIneqPoly:=[];
    for eCompl in TheCompl
    do
      eScal:=eCompl * eIneq;
      Add(eIneqPoly, eScal);
    od;
    Add(ListIneqPoly, eIneqPoly);
  od;
  InequalityComputation:=function(LinearFunc)
    local TheFunc, TheLP, eSol, ePointEXT, ePointSpace, ePointSpann, eScal, i;
    TheFunc:=List(TheComplBasisSpann, x->x*LinearFunc);
    TheLP:=LinearProgramming(ListIneqPoly, TheFunc);
    eSol:=FindSolutionToLinearProgram(ListIneqPoly, TheFunc);
    ePointEXT:=eSolPoint;
    for i in [1..Length(eSol)]
    do
      ePointEXT:=ePointEXT + eSol[i]*BasisLin[i];
    od;
    ePointSpace:=ePointEXT * EXT;
    ePointSpann:=SolutionMat(BasisSpann, ePointSpace);
    if ePointSpann=fail then
      Error("Please debug from here");
    fi;
    eScal:=LinearFunc*ePointSpann;
    return rec(ePointSpann:=ePointSpann, eScal:=eScal);
  end;
  EXTint:=[];
  FuncInsertEXT:=function(eEXTint)
    local eO, eVect;
    if Position(EXTint, RemoveFraction(eEXTint))<>fail then
      return;
    fi;
    eO:=Orbit(RecGRP.GRPsubspace, eEXTint, OnPoints);
    for eVect in eO
    do
      Add(EXTint, RemoveFraction(eVect));
    od;
#    Print("Now |EXTint|=", Length(EXTint), "\n");
#    Print("EXTint=", EXTint, "\n");
  end;
  ComputeInitialList:=function()
    local idx, LinFunc, i, eRecFAC, nbIter, TheLevel;
    nbIter:=0;
    while(true)
    do
      nbIter:=nbIter+1;
      TheLevel:=5 + UpperInteger(nbIter/100);
      LinFunc:=[];
      for i in [1..DimSpace]
      do
        Add(LinFunc, Random([-TheLevel..TheLevel]));
      od;
      eRecFAC:=InequalityComputation(LinFunc);
      FuncInsertEXT(eRecFAC.ePointSpann);
      if RankMat(EXTint)=DimSpace then
        break;
      fi;
    od;
  end;
  GetPermGRPvert:=function()
    local ListPermGens, eGen, eList, ePerm;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(RecGRP.GRPsubspace)
    do
      eList:=List(EXTint, x->Position(EXTint, RemoveFraction(x*eGen)));
      ePerm:=PermList(eList);
      Add(ListPermGens, ePerm);
    od;
    return PersoGroupPerm(ListPermGens);
  end;
  #
  ComputeInitialList();
  #
  while(true)
  do
    GRPext:=GetPermGRPvert();
    LOrbFAC:=DualDescriptionStandard(EXTint, GRPext);
    Print("|EXTint|=", Length(EXTint), "  |GRPext|=", Order(GRPext), "  |LOrbFAC|=", Length(LOrbFAC), "\n");
    IsComplete:=true;
    EXTsave:=StructuralCopy(EXTint);
    for eRepr in LOrbFAC
    do
#      Print("eRepr=", eRepr, "\n");
      eFAC:=__FindFacetInequality(EXTsave, eRepr);
      eRecFAC:=InequalityComputation(eFAC);
#      Print("eRecFAC.eScal=", eRecFAC.eScal, "\n");
      if eRecFAC.eScal<>0 then
        FuncInsertEXT(eRecFAC.ePointSpann);
        IsComplete:=false;
      fi;
    od;
    if IsComplete then
      break;
    fi;
  od;
  Print("Final |EXT|=", Length(EXTint), " |GRPext|=", Order(GRPext), " |LOrbFAC|=", Length(LOrbFAC), "\n");
  return rec(TotRec:=TotRec, EXT:=EXTint, GRPext:=GRPext, GRPsubspace:=RecGRP.GRPsubspace, LOrbFAC:=LOrbFAC);
end;

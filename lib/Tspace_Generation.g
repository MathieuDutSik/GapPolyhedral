ConstructQuotientGroup:=function(GramMat, GrpChar, NormalSub)
  local n, LNorm, ListVectorOrbits, ListGenMat, TheIndex, CurrentNorm, FuncConstruction, OrderQuotientGRP, Lcons, SHV, iV, eV, LOrb, IsFinished, eOrb, SmOrbs, EWR, TheConstr, eSmOrb, NewOrd;
  n:=Length(GramMat);
  LNorm:=Set(List([1..n], x->GramMat[x][x]));
  ListVectorOrbits:=[];
  ListGenMat:=GeneratorsOfGroup(GrpChar);
  TheIndex:=Order(GrpChar)/Order(NormalSub);
  SHV:=ShortestVectors(GramMat, Minimum(LNorm));
  CurrentNorm:=Minimum(SHV.norms);
  FuncConstruction:=function(ListOrbSmall)
    local ListVect, eSmOrb, ListPermGen, PermGRP, ListPermQUOT, eMat, eList, PermQUOT, phi12, phi21, phi23, FCrevMap;
    ListVect:=[];
    for eSmOrb in ListOrbSmall
    do
      Append(ListVect, eSmOrb);
    od;
    ListPermGen:=List(ListGenMat, x->PermList(List(ListVect, y->Position(ListVect, y*x))));
    PermGRP:=Group(ListPermGen);
    #
    ListPermQUOT:=[];
    for eMat in ListGenMat
    do
      eList:=List(ListOrbSmall, x->Position(ListOrbSmall, Set(x*eMat)));
      Add(ListPermQUOT, PermList(eList));
    od;
    PermQUOT:=Group(ListPermQUOT);
    #
    phi12:=GroupHomomorphismByImagesNC(GrpChar, PermGRP, ListGenMat, ListPermGen);
    phi21:=GroupHomomorphismByImagesNC(PermGRP, GrpChar, ListPermGen, ListGenMat);
    phi23:=GroupHomomorphismByImagesNC(PermGRP, PermQUOT, ListPermGen, ListPermQUOT);
    #
    FCrevMap:=function(QuotSub)
      local ListGen, eGen, fGen, gGen;
      ListGen:=ShallowCopy(NormalSub.ListMat);
      for eGen in GeneratorsOfGroup(QuotSub)
      do
        fGen:=PreImagesRepresentative(phi23, eGen);
        gGen:=Image(phi21, fGen);
        Add(ListGen, gGen);
      od;
      return Group(ListGen);
    end;
    return rec(GRPmat:=GrpChar, PermGRP:=PermGRP, PermQUOT:=PermQUOT, phi12:=phi12, phi21:=phi21, phi23:=phi23, FCrevMap:=FCrevMap);
  end;
  OrderQuotientGRP:=1;
  while(true)
  do
    Lcons:=[];
    SHV:=ShortestVectors(GramMat, CurrentNorm);
    for iV in [1..Length(SHV.vectors)]
    do
      if SHV.norms[iV]=CurrentNorm then
        eV:=SHV.vectors[iV];
        Add(Lcons, eV);
        Add(Lcons, -eV);
      fi;
    od;
    LOrb:=Orbits(GrpChar, Lcons, OnPoints);
    IsFinished:=false;
    for eOrb in LOrb
    do
      SmOrbs:=Orbits(NormalSub, eOrb, OnPoints);
      EWR:=ShallowCopy(ListVectorOrbits);
      for eSmOrb in SmOrbs
      do
        AddSet(EWR, Set(eSmOrb));
      od;
      TheConstr:=FuncConstruction(EWR);
      NewOrd:=Order(TheConstr.PermQUOT);
      if NewOrd>OrderQuotientGRP then
        ListVectorOrbits:=ShallowCopy(EWR);
        OrderQuotientGRP:=NewOrd;
      fi;
      if OrderQuotientGRP=TheIndex then
        IsFinished:=true;
        break;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
    CurrentNorm:=CurrentNorm+1;
  od;
  return TheConstr;
end;







VectorSetToAntipodal:=function(ListVect, MatrixGrp)
  local ListStatus, ListAntipodal, i, eVect, fVect, j, ListGen, MatrGen, eGen, eList, eAnt, eV, PermGRP, phi;
  ListStatus:=ListWithIdenticalEntries(Length(ListVect), 1);
  ListAntipodal:=[];
  for i in [1..Length(ListVect)]
  do
    if ListStatus[i]=1 then
      eVect:=ListVect[i];
      fVect:=-eVect;
      j:=Position(ListVect, fVect);
      ListStatus[j]:=0;
      Add(ListAntipodal, Set([i,j]));
    fi;
  od;
  ListGen:=[];
  MatrGen:=GeneratorsOfGroup(MatrixGrp);
  for eGen in MatrGen
  do
    eList:=[];
    for eAnt in ListAntipodal
    do
      eV:=Set(List(eAnt, x->Position(ListVect, ListVect[x]*eGen)));
      Add(eList, Position(ListAntipodal, eV));
    od;
    Add(ListGen, PermList(eList));
  od;
  Print("Creating perm group on ", Length(ListAntipodal), " elements\n");
  PermGRP:=Group(ListGen);
  phi:=GroupHomomorphismByImagesNC(MatrixGrp, PermGRP, MatrGen, ListGen);
  return rec(PermGRP:=PermGRP, phi:=phi);
end;







#
#
# A list of subgroup is provided together with their inclusions
# and the maximal one are extracted together with their inclusions
#
Method1ExtractBravaisSubgroups:=function(CJmat, TheOrg, ListBasis, ListOrder)
  local ListStatus, ListDimension, iCJ, eCJ, eAdj, jCJ, kCJ, ListCases, RenormalizedOrg, RenormalizedSec, LSet, LSub, RenormalizedThi, GiveAllSubConjugacyClasses, VSet, Renormalized4th, ReverseInclusion, iCase, ListBravais;
  ListStatus:=ListWithIdenticalEntries(Length(CJmat), 1);
  ListDimension:=List(ListBasis, Length);
  RenormalizedOrg:=[];
  for iCJ in [1..Length(CJmat)]
  do
    LSub:=Union(TheOrg[iCJ], x->x[1]);
    Add(RenormalizedOrg, LSub);
  od;
  for iCJ in [1..Length(CJmat)]
  do
    for eAdj in TheOrg[iCJ]
    do
      jCJ:=eAdj[1];
      if ListDimension[jCJ]=ListDimension[iCJ] then
        ListStatus[jCJ]:=0;
        for kCJ in [1..Length(CJmat)]
        do
          if jCJ in RenormalizedOrg[kCJ] then
            RenormalizedOrg[kCJ]:=Union(RenormalizedOrg[kCJ], RenormalizedOrg[jCJ]);
            RemoveSet(RenormalizedOrg[kCJ], jCJ);
          fi;
        od;
      fi;
    od;
  od;
  for iCJ in [1..Length(CJmat)]
  do
    if ListStatus[iCJ]=0 then
      RenormalizedOrg[iCJ]:=[];
    fi;
  od;
  ListCases:=Filtered([1..Length(CJmat)], x->ListStatus[x]=1);

  RenormalizedSec:=[];
  for eCJ in ListCases
  do
    LSet:=List(RenormalizedOrg[eCJ], x->Position(ListCases, x));
    Add(RenormalizedSec, LSet);
  od;
  GiveAllSubConjugacyClasses:=function(iCJ)
    local ListDone, ListUndone, NewList, fCJ;
    ListDone:=[];
    ListUndone:=[iCJ];
    while(Length(ListUndone)>0)
    do
      NewList:=[];
      for fCJ in ListUndone
      do
        AddSet(ListDone, fCJ);
        NewList:=Union(NewList, RenormalizedSec[fCJ]);
      od;
      ListUndone:=ShallowCopy(NewList);
    od;
    return ListDone;
  end;
  RenormalizedThi:=[];
  for iCJ in [1..Length(ListCases)]
  do
    VSet:=GiveAllSubConjugacyClasses(iCJ);
    RemoveSet(VSet, iCJ);
    RenormalizedThi[iCJ]:=VSet;
  od;
  Renormalized4th:=[];
  for iCJ in [1..Length(ListCases)]
  do
    VSet:=[];
    for kCJ in RenormalizedThi[iCJ]
    do
      VSet:=Union(VSet, RenormalizedThi[kCJ]);
    od;
    Renormalized4th[iCJ]:=Difference(RenormalizedThi[iCJ], VSet);
  od;
  ReverseInclusion:=[];
  for iCJ in [1..Length(ListCases)]
  do
    ReverseInclusion[iCJ]:=[];
  od;
  for iCJ in [1..Length(ListCases)]
  do
    for jCJ in Renormalized4th[iCJ]
    do
      AddSet(ReverseInclusion[jCJ], iCJ);
    od;
  od;
  ListBravais:=[];
  for iCase in [1..Length(ListCases)]
  do
    Add(ListBravais, rec(ListGen:=GeneratorsOfGroup(CJmat[ListCases[iCase]]), Basis:=ListBasis[ListCases[iCase]], Order:=ListOrder[ListCases[iCase]], SubGroups:=Renormalized4th[iCase], SuperGroups:=ReverseInclusion[iCase]));
  od;
  return ListBravais;
end;










Method2ExtractBravaisSubgroups:=function(CJmat)
  local ListBasis, iCJ, eCJ, TheBasis, GramMat, ListGroup, TheTotalGroup;
  ListBasis:=[];
  for iCJ in [1..Length(CJmat)]
  do
    eCJ:=CJmat[iCJ];
    TheBasis:=InvariantFormDutourVersion(GeneratorsOfGroup(eCJ));
    Add(ListBasis, TheBasis);
    if Length(TheBasis)=1 then
      GramMat:=TheBasis[1];
    fi;
  od;
  ListGroup:=[];
  for iCJ in [1..Length(CJmat)]
  do
    TheTotalGroup:=FindFullSymmetrySpace(ListBasis[iCJ], GramMat);
    Add(ListGroup, TheTotalGroup);
  od;
  Error("Finalize program from that point");
end;










FunctionGiveMaximalSymmetries:=function(IMFGRP)
  local U, phi, GramMat, GrpChar, NormalSub, TheOrd, GRPmat, Latt, TheOrg, CJ, CJmat, ListBasis, eCJ, Repr, MatrRepr, ListGensSpec, n, ListCases, ListOrder, TheConstr, NewListCases, eCase, SVR;
  U:=ImfRecord(IMFGRP);
  GramMat:=U.form;
  n:=Length(U.form);
  phi:=IsomorphismPermGroup(IMFGRP);
  TheOrd:=Order(Image(phi));
  #
  Print("|G|=", TheOrd, "\n");
  Print("type=", U.isomorphismType, "\n");
  #
  GRPmat:=PreImage(phi);
  SVR:=__ExtractInvariantFaithfulFamilyShortVector(GramMat, rec(ListMat:=GeneratorsOfGroup(GRPmat), order:=TheOrd));
  GrpChar:=rec(ListMat:=GeneratorsOfGroup(GRPmat), order:=Order(Image(phi)));
  NormalSub:=rec(ListMat:=[-IdentityMat(n)], order:=2);
  TheConstr:=ConstructQuotientGroup(GramMat, GrpChar, NormalSub);
  Latt:=LatticeSubgroups(TheConstr.PermGRP);
  TheOrg:=MaximalSubgroupsLattice(Latt);
  CJ:=ConjugacyClassesSubgroups(Latt);
  Print("Find ", Length(CJ), " conjugacy classes\n");

  CJmat:=[];
  ListBasis:=[];
  ListOrder:=[];
  for eCJ in CJ
  do
    Repr:=Representative(eCJ);
    MatrRepr:=PreImage(TheConstr.phi, Repr);
    ListGensSpec:=GeneratorsOfGroup(MatrRepr);
    Add(ListBasis, InvariantFormDutourVersion(ListGensSpec));
    Add(ListOrder, 2*Order(Repr));
    Add(CJmat, MatrRepr);
  od;
  ListCases:=Method1ExtractBravaisSubgroups(CJmat, TheOrg, ListBasis, ListOrder);
  NewListCases:=[];
  for eCase in ListCases
  do
    Add(NewListCases, rec(Basis:=eCase.Basis, ListGen:=eCase.ListGen, Order:=eCase.Order, IsBravaisSpace:=true, SuperMat:=GramMat, CharacteristicFamilyVector:=SVR));
  od;
  return NewListCases;
end;




TspaceFromOrthogonal:=function(GramMat, V)
  local Bmat, V2;
  V2:=[V];
  Bmat:=GramMat*TransposedMat(V2)*V2*GramMat;
  return [Bmat, GramMat];
end;




TspaceLamination:=function(GramMat, SingleDelaunay)
  local TheBasis, n, H, K, i, j, ListGen, ListGenDelaunay, eMat, TheExpl, W, NewMat, SPA, eCentRed, SuperMat, v, Ord, IsBravaisSpace, SVR;
  n:=Length(GramMat);
  H:=NullMat(n+1, n+1);
  for i in [1..n]
  do
    for j in [1..n]
    do
      H[i][j]:=GramMat[i][j];
    od;
  od;
  eCentRed:=SingleDelaunay.Center{[2..n+1]};
  Print("eCentRed=", eCentRed, "\n");
  v:=eCentRed*GramMat;
  Print("v=", v, "\n");
  for i in [1..n]
  do
    H[i][n+1]:=v[i];
    H[n+1][i]:=v[i];
  od;
  H:=RemoveFractionMatrix(H);
  K:=NullMat(n+1, n+1);
  K[n+1][n+1]:=1;
  TheBasis:=[H,K];
  SuperMat:=H;
  while(true)
  do
    if IsPositiveDefiniteSymmetricMatrix(SuperMat)=false then
      SuperMat:=SuperMat+K;
    else
      break;
    fi;
  od;
  Ord:=SingleDelaunay.TheStab.Order;
  ListGen:=[];
  ListGenDelaunay:=GeneratorsOfGroup(Image(SingleDelaunay.TheStab.PhiPermMat));
  for eMat in ListGenDelaunay
  do
    TheExpl:=FuncExplodeBigMatrix(eMat);
    NewMat:=[];
    Print("eMat=\n");
    PrintArray(TheExpl.MatrixTransformation);
    for i in [1..n]
    do
      W:=TheExpl.MatrixTransformation[i];
      Add(W, 0);
      Add(NewMat, W);
    od;
    W:=-TheExpl.eTrans;
    Add(W, 1);
    Add(NewMat, W);
    Add(ListGen, NewMat);
  od;
  W:=2*eCentRed;
  if IsIntegralVector(W)=true then
    NewMat:=IdentityMat(n+1);
    NewMat[n+1][n+1]:=-1;
    for i in [1..n]
    do
      NewMat[n+1][i]:=W[i];
    od;
    Add(ListGen, NewMat);
  else
    Add(ListGen, -IdentityMat(n+1));
  fi;
  Ord:=Ord*2;
  SPA:=InvariantFormDutourVersion(ListGen);
  if Length(SPA)=2 then
    IsBravaisSpace:=true;
  else
    IsBravaisSpace:=false;
  fi;
  SVR:=__ExtractInvariantFaithfulFamilyShortVector(SuperMat, rec(ListMat:=ListGen, order:=Ord));
  return rec(Basis:=TheBasis, Order:=Ord, IsBravaisSpace:=IsBravaisSpace, ListGen:=ListGen, SuperMat:=SuperMat, CharacteristicFamilyVector:=SVR);
end;



CorrectnessRealQuadratic:=function(eSum, eProd)
  local TheDiscriminant, ListMult, pos, TheRes;
  if eSum=0 then
    TheDiscriminant:=-eProd;
  else
    TheDiscriminant:=eSum*eSum -4*eProd;
  fi;
  TheRes:=TheDiscriminant mod 4;
  if TheDiscriminant<=0 then
    Print("The Field is not real quadratic, impossible to work\n");
    return false;
  fi;
  ListMult:=List(Collected(FactorsInt(TheDiscriminant)), x->x[2]);
  pos:=First(ListMult, x->x mod 2=0);
  if pos<>fail then
    Print("TheDiscriminant=", TheDiscriminant, "\n");
    Print("The Discriminant has a square factor, illegal\n");
    return false;
  fi;
  return true;
end;


SquareFreeDecomposition:=function(eInt)
  local eProdRed, eProdIrred, LFac, eEnt, res, eExpo;
  eProdRed:=1;
  eProdIrred:=1;
  LFac:=Collected(FactorsInt(eInt));
  for eEnt in LFac
  do
    res:=eEnt[2] mod 2;
    if res=1 then
      eProdIrred:=eProdIrred*eEnt[1];
    fi;
    eExpo:=(eEnt[2] - res)/2;
    eProdRed:=eProdRed*(eEnt[1]^(eExpo));
  od;
  return rec(eProdRed:=eProdRed, eProdIrred:=eProdIrred);
end;



GetSpaceRealQuadratic:=function(n, eSum, eProd)
  local TheDiscriminant, ListMult, pos, ListMatrix, i, j, eMat, ListBC, TheBasis, GetFromPair, eRecBC, Bmat, Cmat, SuperMat, Imultiplication, IsInSL, IsInGL, TrivialFilter, eDelta, alpha, IsTotallyPositive, eRecDecompo, GetPair;
  if CorrectnessRealQuadratic(eSum, eProd)=false then
    Error("Incorrect discriminant, retry");
  fi;
  eDelta:=eSum*eSum - 4*eProd;
  alpha:=(eSum + Sqrt(eDelta))/2;
  eRecDecompo:=SquareFreeDecomposition(eDelta);
  ListMatrix:=[];
  for i in [1..n]
  do
    for j in [i..n]
    do
      eMat:=NullMat(n,n);
      eMat[i][j]:=1;
      eMat[j][i]:=1;
      Add(ListMatrix, eMat);
    od;
  od;
  ListBC:=[];
  for eMat in ListMatrix
  do
    Add(ListBC, rec(B:=NullMat(n,n), C:=eMat));
  od;
  for eMat in ListMatrix
  do
    Add(ListBC, rec(B:=eMat, C:=NullMat(n,n)));
  od;
  TheBasis:=[];
  GetFromPair:=function(Bmat, Cmat)
    local fMat, i, j, eVal1, eVal1b, eVal2;
    fMat:=NullMat(2*n,2*n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        eVal1:=2*Bmat[i][j] + eSum*Cmat[i][j];
        eVal1b:=(eSum*eSum-2*eProd)*Bmat[i][j] + eSum*eProd*Cmat[i][j];
        fMat[i][j]:=eVal1;
        fMat[n+i][n+j]:=eVal1b;
        eVal2:=eSum*Bmat[i][j] + 2*eProd*Cmat[i][j];
        fMat[n+i][j]:=eVal2;
        fMat[i][n+j]:=eVal2;
      od;
    od;
    return fMat;
  end;
  for eRecBC in ListBC
  do
    Bmat:=eRecBC.B;
    Cmat:=eRecBC.C;
    Add(TheBasis, GetFromPair(Bmat, Cmat));
  od;
  SuperMat:=GetFromPair(IdentityMat(n), NullMat(n,n));
  Imultiplication:=NullMat(2*n,2*n);
  for i in [1..n]
  do
    Imultiplication[i][n+i]:=1;
    Imultiplication[n+i][i]:=-eProd;
    Imultiplication[n+i][n+i]:=eSum;
  od;
  IsInGL:=function(eMat)
    if eMat*Imultiplication<>Imultiplication*eMat then
      return false;
    fi;
    return true;
  end;
  TrivialFilter:=function(eMat)
    return true;
  end;
  GetPair:=function(eMat)
    local A11, A12, A21, A22, Amat, Bmat;
    A11:=List(eMat{[1..n]}, x->x{[1..n]});
    A12:=List(eMat{[1..n]}, x->x{[n+1..2*n]});
    A21:=List(eMat{[n+1..2*n]}, x->x{[1..n]});
    A22:=List(eMat{[n+1..2*n]}, x->x{[n+1..2*n]});
    Amat:=A11;
    Bmat:=A12;
    if A21 <> -eProd*Bmat then
      Error("Conceptual error 1");
    fi;
    if A22 <> Amat + eSum*Bmat then
      Error("Conceptual error 2");
    fi;
    return rec(Amat:=Amat, Bmat:=Bmat);
  end;
  IsInSL:=function(eMat)
    local ePair, Amat, Bmat, eMatRes, TheDet;
    ePair:=GetPair(eMat);
    Amat:=ePair.Amat;
    Bmat:=ePair.Bmat;
    eMatRes:=Amat + alpha*Bmat;
    TheDet:=DeterminantMat(eMatRes);
    if TheDet=1 then
      return true;
    fi;
    return false;
  end;
  IsTotallyPositive:=function(eMat)
    local ePair, Amat, Bmat, alpha1, alpha2, eMatRes1, eMatRes2, TheDet1, TheDet2, test1, test2;
    ePair:=GetPair(eMat);
    Amat:=ePair.Amat;
    Bmat:=ePair.Bmat;
    alpha1:=(eSum + eRecDecompo.eProdRed*Sqrt(eRecDecompo.eProdIrred))/2;
    alpha2:=(eSum - eRecDecompo.eProdRed*Sqrt(eRecDecompo.eProdIrred))/2;
    eMatRes1:=Amat + alpha1*Bmat;
    eMatRes2:=Amat + alpha2*Bmat;
    TheDet1:=DeterminantMat(eMatRes1);
    TheDet2:=DeterminantMat(eMatRes2);
    test1:=QN_IsPositive(eRecDecompo.eProdIrred, TheDet1);
    test2:=QN_IsPositive(eRecDecompo.eProdIrred, TheDet2);
    if test1=true and test2=true then
      return true;
    fi;
    return false;
  end;
  return rec(Basis:=TheBasis,
             SuperMat:=SuperMat,
             ScalProdMatrix:=GetScalProdMatrix(TheBasis, SuperMat), 
             ListComm:=[Imultiplication], 
             IsInSL:=IsInSL, IsInGL:=IsInGL,
             TrivialFilter:=TrivialFilter, 
             IsTotallyPositive:=IsTotallyPositive,
             PtWiseStab:=Group([IdentityMat(2*n)]),
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
             ShortestFunction:=ShortestVectorDutourVersion);
end;


PrintQuaternionAlgebra:=function(output, QuartAlg)
  AppendTo(output, "Quaternion algebra (a,b/Q)\n");
  AppendTo(output, "a=", QuartAlg.a, "\n");
  AppendTo(output, "b=", QuartAlg.b, "\n");
  AppendTo(output, "Maximal order considered\n");
  WriteMatrix(output, QuartAlg.BasisQuart);
end;


# we design the space for a basis of quaternion matrices.
# The Quaternion algebra is written as (a,b/Q) with
# i^2 = a, j^2=b and ij = -ji
# Basis of the space is {1,i,j,k=ij}
# The BasisQuart is typically a maximal order in the quaternion
# algebra
GetRationalQuaternionAlgebra:=function(n, QuartAlg)
  local QuaternionProduct, QuaternionConj, FunctionGetMatrix, TheBasis, GetZerMatrix, idx, i, j, k, eEnt, HamiltonianMatrix, IsInSL, IsInGL, TrivialFilter, eLine, ListComm, eVQ, eQuart, eBlock, SuperMat, eSol, eProd, eMulti, u, v, RandomQuart, CheckAssociativity, a, b, BasisQuart, BasisCommutation;
  a:=QuartAlg.a;
  b:=QuartAlg.b;
  BasisQuart:=QuartAlg.BasisQuart;
  QuaternionProduct:=function(x, y)
    local z1, z2, z3, z4;
    z1:=x[1]*y[1] + a*x[2]*y[2] + b*x[3]*y[3] - a*b*x[4]*y[4];
    z2:=x[2]*y[1] +   x[1]*y[2] - b*x[3]*y[4] +   b*x[4]*y[3];
    z3:=x[3]*y[1] +   x[1]*y[3] + a*x[2]*y[4] -   a*x[4]*y[2];
    z4:=x[4]*y[1] +   x[1]*y[4] +   x[2]*y[3] -     x[3]*y[2];
    return [z1, z2, z3, z4];
  end;
  QuaternionConj:=function(x)
    return [x[1], -x[2], -x[3], -x[4]];
  end;
  FunctionGetMatrix:=function(HamiltonianMatrix)
    local TheBigMat, i, j, eHamil, u, v, uHamil, vHamil, eProd;
    TheBigMat:=NullMat(4*n, 4*n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        eHamil:=HamiltonianMatrix[i][j];
        for u in [1..4]
        do
          for v in [1..4]
          do
            uHamil:=BasisQuart[u];
            vHamil:=QuaternionConj(BasisQuart[v]);
            eProd:=QuaternionProduct(QuaternionProduct(uHamil, eHamil), vHamil);
            TheBigMat[4*(i-1)+u][4*(j-1)+v]:=TheBigMat[4*(i-1)+u][4*(j-1)+v] + eProd[1];
          od;
        od;
      od;
    od;
    return TheBigMat;
  end;
  RandomQuart:=function()
    local x, i;
    x:=[];
    for i in [1..4]
    do
      Add(x, Random([-10..10]));
    od;
    return x;
  end;
  CheckAssociativity:=function()
    local x, y, z, eProd1, eProd2, iter;
    for iter in [1..100]
    do
      x:=RandomQuart();
      y:=RandomQuart();
      z:=RandomQuart();
      eProd1:=QuaternionProduct(QuaternionProduct(x, y), z);
      eProd2:=QuaternionProduct(x, QuaternionProduct(y, z));
      if eProd1<>eProd2 then
        Error("Associativity error");
      fi;
    od;
  end;
  CheckAssociativity();
  TheBasis:=[];
  GetZerMatrix:=function()
    local i, j, HamiltonianMatrix, eLine, eEnt;
    HamiltonianMatrix:=[];
    for i in [1..n]
    do
      eLine:=[];
      for j in [1..n]
      do
        eEnt:=[0,0,0,0];
        Add(eLine, eEnt);
      od;
      Add(HamiltonianMatrix, eLine);
    od;
    return HamiltonianMatrix;
  end;
  for idx in [1..n]
  do
    HamiltonianMatrix:=GetZerMatrix();
    HamiltonianMatrix[idx][idx]:=[1,0,0,0];
    Add(TheBasis, FunctionGetMatrix(HamiltonianMatrix));
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      for k in [1..4]
      do
        eEnt:=[0,0,0,0];
        eEnt[k]:=1;
        HamiltonianMatrix:=GetZerMatrix();
        HamiltonianMatrix[i][j]:=eEnt;
        HamiltonianMatrix[j][i]:=QuaternionConj(eEnt);
        Add(TheBasis, FunctionGetMatrix(HamiltonianMatrix));
      od;
    od;
  od;
  #
  HamiltonianMatrix:=[];
  for i in [1..n]
  do
    eLine:=[];
    for j in [1..n]
    do
      if i=j then
        eEnt:=[1,0,0,0];
      else
        eEnt:=[0,0,0,0];
      fi;
      Add(eLine, eEnt);
    od;
    Add(HamiltonianMatrix, eLine);
  od;
  SuperMat:=FunctionGetMatrix(HamiltonianMatrix);
  #
  ListComm:=[];
  for i in [2..4]
  do
    eQuart:=ListWithIdenticalEntries(4,0);
    eQuart[i]:=1;
    eBlock:=[];
    for eVQ in BasisQuart
    do
      eProd:=QuaternionProduct(eQuart, eVQ);
      eSol:=SolutionMat(BasisQuart, eProd);
      Add(eBlock, eSol);
    od;
    eMulti:=NullMat(4*n, 4*n);
    for j in [1..n]
    do
      for u in [1..4]
      do
        for v in [1..4]
        do
          eMulti[(j-1)*4 + u][(j-1)*4 + v]:=eBlock[u][v];
        od;
      od;
    od;
    Add(ListComm, eMulti);
  od;
  IsInGL:=function(eMat)
    local Imultiplication;
    for Imultiplication in ListComm
    do
      if eMat*Imultiplication<>Imultiplication*eMat then
        return false;
      fi;
    od;
    return true;
  end;
  IsInSL:=function(eMat)
    Error("Need to program the Dieudonne determinant");
  end;
  TrivialFilter:=function(eMat)
    return true;
  end;
  BasisCommutation:=BasesCommutingMatrices(ListComm);
  if Length(BasisCommutation)<>4*n*n then
    Error("Some long held idea is proved false");
  fi;
  return rec(Basis:=TheBasis,
             SuperMat:=SuperMat,
             ScalProdMatrix:=GetScalProdMatrix(TheBasis, SuperMat), 
             ListComm:=ListComm, 
             IsInSL:=IsInSL, IsInGL:=IsInGL,
             TrivialFilter:=TrivialFilter, 
             PtWiseStab:=Group([IdentityMat(4*n)]),
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
             ShortestFunction:=ShortestVectorDutourVersion);
end;




GetTotallyRealFieldExpression:=function(n, ListS)
  local TheDeg, ThePowExpo, ListPowSums, ListMatrix, i, j, eMat, TheBigDim, GetPow, GetBigExpression, eCaseSuper, Imultiplication, eVal, IsInGL, TrivialFilter, TheBasis, eCase, TheSuperMat, eMatrix, ListMat, TheBasisExpr, eMatB;
  TheDeg:=Length(ListS);
  ThePowExpo:=3*(TheDeg-1);
  ListPowSums:=GetNewtonSums(ListS, ThePowExpo);
  ListMatrix:=[];
  for i in [1..n]
  do
    for j in [i..n]
    do
      eMat:=NullMat(n,n);
      eMat[i][j]:=1;
      eMat[j][i]:=1;
      Add(ListMatrix, eMat);
    od;
  od;
  TheBigDim:=TheDeg*n;
  GetPow:=function(idx)
    if idx=0 then
      return TheDeg;
    fi;
    return ListPowSums[idx];
  end;
  GetBigExpression:=function(ListMat)
    local eBigMat, i, j, k, SumPow, i2, j2;
    eBigMat:=NullMat(TheBigDim, TheBigDim);
    for i in [0..TheDeg-1]
    do
      for j in [0..TheDeg-1]
      do
        for k in [0..TheDeg-1]
        do
          SumPow:=GetPow(i+j+k);
          for i2 in [1..n]
          do
            for j2 in [1..n]
            do
              eBigMat[i*n + i2][j*n + j2]:=eBigMat[i*n + i2][j*n + j2] + SumPow*ListMat[k+1][i2][j2];
            od;
          od;
        od;
      od;
    od;
    return eBigMat;
  end;
  TheBasis:=[];
  for i in [1..TheDeg]
  do
    for eMatrix in ListMatrix
    do
      ListMat:=[];
      for j in [1..TheDeg]
      do
        if i<>j then
          Add(ListMat, NullMat(n,n));
        else
          Add(ListMat, eMatrix);
        fi;
      od;
      Add(TheBasis, GetBigExpression(ListMat));
    od;
  od;
  TheBasisExpr:=List(TheBasis, SymmetricMatrixToVector);
  eCaseSuper:=[IdentityMat(n)];
  for i in [2..TheDeg]
  do
    Add(eCaseSuper, NullMat(n,n));
  od;
  TheSuperMat:=GetBigExpression(eCaseSuper);
  Imultiplication:=NullMat(TheBigDim, TheBigDim);
  for j in [1..TheDeg-1]
  do
    for i in [1..n]
    do
      Imultiplication[i + (j-1)*n][i + j*n]:=1;
    od;
  od;
  for j in [1..TheDeg]
  do
    eVal:=(-1)^(TheDeg-j)*ListS[1+TheDeg-j];
    for i in [1..n]
    do
      Imultiplication[i + (TheDeg-1)*n][i + (j-1)*n]:=eVal;
    od;
  od;
  for eMat in TheBasis
  do
    eMatB:=Imultiplication*eMat*TransposedMat(Imultiplication);
    if SolutionMat(TheBasisExpr, SymmetricMatrixToVector(eMatB))=fail then
      Error("Bug at that point");
    fi;
  od;
  IsInGL:=function(eMat)
    if eMat*Imultiplication<>Imultiplication*eMat then
      return false;
    fi;
    return true;
  end;
  TrivialFilter:=function(eMat)
    return true;
  end;
  return rec(Basis:=TheBasis,
             SuperMat:=TheSuperMat,
             ScalProdMatrix:=GetScalProdMatrix(TheBasis, TheSuperMat), 
             ListComm:=[Imultiplication], 
             IsInGL:=IsInGL,
             TrivialFilter:=TrivialFilter, 
             PtWiseStab:=Group([IdentityMat(TheDeg*n)]),
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
             ShortestFunction:=ShortestVectorDutourVersion);
end;



CorrectnessImaginaryQuadratic:=function(eSum, eProd)
  local TheDiscriminant, ListMult, pos, TheRes, eDiv, LFact;
  if eSum=0 then
    TheDiscriminant:=-4*eProd;
  else
    TheDiscriminant:=eSum*eSum -4*eProd;
  fi;
  TheRes:=TheDiscriminant mod 4;
  Print("eSum=", eSum, " eProd=", eProd, "\n");
  Print("TheDiscriminant=", TheDiscriminant, " TheRes=", TheRes, "\n");
  if TheRes=3 or TheRes=2 then
    Print("We do not allow residue of 3 or 2\n");
    return false;
  fi;
  LFact:=Set(FactorsInt(AbsInt(TheDiscriminant)));
  for eDiv in Difference(LFact, [2])
  do
    if IsInt(TheDiscriminant/(eDiv*eDiv)) then
      Print("We have ", eDiv, " as a square divisor. Not allowed\n");
      return false;
    fi;
  od;
  if TheDiscriminant>=0 then
    Print("The Field is not imaginary quadratic, impossible to work\n");
    return false;
  fi;
  if TheDiscriminant=-1 then
    return true;
  fi;
  ListMult:=List(Collected(FactorsInt(-TheDiscriminant)), x->x[2]);
  pos:=First(ListMult, x->x mod 2=0);
  if pos<>fail then
    Print("eSum=", eSum, "  eProd=", eProd, "\n");
    Print("TheDiscriminant=", TheDiscriminant, "\n");
    Print("The Discriminant has a square factor, illegal\n");
#    return false;
  fi;
  return true;
end;


GetStandardIntegralVoronoiSpace:=function(n)
  local TheSuperMat, TheBasis, i, j, eMat, Imultiplication, eScal, TheFilter;
  TheBasis:=[];
  for i in [1..n]
  do
    for j in [i..n]
    do
      eMat:=NullMat(n, n);
      if i=j then
        eScal:=1;
      else
        eScal:=1/2;
      fi;
      eMat[i][j]:=eScal;
      eMat[j][i]:=eScal;
      Add(TheBasis, eMat);
    od;
  od;
  TheSuperMat:=LatticeAn(n).GramMat/2;
  TheFilter:=function(eMat)
    return true;
  end;
  return rec(n:=n, 
             Basis:=TheBasis, 
             SuperMat:=TheSuperMat,
             ScalProdMatrix:=GetScalProdMatrix(TheBasis, TheSuperMat), 
             ListComm:=[], 
             TheFilter:=TheFilter,
             PtWiseStab:=Group([IdentityMat(n)]),
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
             ShortestFunction:=ShortestVectorDutourVersion);
end;




GetStandardVoronoiSpace:=function(n)
  local TheSuperMat, TheBasis, i, j, eMat, Imultiplication, IsInSL, TrivialFilter, TheFilter;
  TheSuperMat:=IdentityMat(n);
  TheBasis:=[];
  for i in [1..n]
  do
    for j in [i..n]
    do
      eMat:=NullMat(n, n);
      eMat[i][j]:=1;
      eMat[j][i]:=1;
      Add(TheBasis, eMat);
    od;
  od;
  IsInSL:=function(eMat)
    local TheDet;
    TheDet:=DeterminantMat(eMat);
    if TheDet=1 then
      return true;
    fi;
    return false;
  end;
  TrivialFilter:=function(eMat)
    return true;
  end;
  TheFilter:=TrivialFilter;
  return rec(Basis:=TheBasis, 
             SuperMat:=TheSuperMat,
             ScalProdMatrix:=GetScalProdMatrix(TheBasis, TheSuperMat), 
             TheFilter:=TrivialFilter,
             ListComm:=[], 
             PtWiseStab:=Group([IdentityMat(n)]),
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
             ShortestFunction:=ShortestVectorDutourVersion);
end;




GetSpaceImaginaryQuadratic:=function(n, eSum, eProd)
  local TheSuperMat, TheBasis, i, j, eMat, Imultiplication, IsInSL, IsInGL, TrivialFilter;
  if CorrectnessImaginaryQuadratic(eSum, eProd)=false then
    Error("Incorrect discriminant, retry");
  fi;
  TheSuperMat:=NullMat(2*n,2*n);
  for i in [1..n]
  do
    TheSuperMat[i][i]:=1;
    TheSuperMat[n+i][i]:=eSum/2;
    TheSuperMat[i][n+i]:=eSum/2;
    TheSuperMat[n+i][n+i]:=eProd;
  od;
  TheBasis:=[];
  for i in [1..n]
  do
    for j in [i..n]
    do
      eMat:=NullMat(2*n, 2*n);
      eMat[i][j]:=1;
      eMat[j][i]:=1;
      #
      eMat[n+i][j]:=eSum/2;
      eMat[n+j][i]:=eSum/2;
      #
      eMat[i][n+j]:=eSum/2;
      eMat[j][n+i]:=eSum/2;
      #
      eMat[n+i][n+j]:=eProd;
      eMat[n+j][n+i]:=eProd;
      Add(TheBasis, eMat);
    od;
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      eMat:=NullMat(2*n, 2*n);
      eMat[n+i][j]:=1;
      eMat[n+j][i]:=-1;
      #
      eMat[i][n+j]:=-1;
      eMat[j][n+i]:=1;
      Add(TheBasis, eMat);
    od;
  od;
  Imultiplication:=NullMat(2*n,2*n);
  for i in [1..n]
  do
    Imultiplication[i][n+i]:=1;
    Imultiplication[n+i][i]:=-eProd;
    Imultiplication[n+i][n+i]:=eSum;
  od;
  IsInGL:=function(eMat)
    if eMat*Imultiplication<>Imultiplication*eMat then
      return false;
    fi;
    return true;
  end;
  TrivialFilter:=function(eMat)
    return true;
  end;
  IsInSL:=function(eMat)
    local A11, A12, A21, A22, Amat, Bmat, eDelta, alpha, eMatRes, TheDet;
    A11:=List(eMat{[1..n]}, x->x{[1..n]});
    A12:=List(eMat{[1..n]}, x->x{[n+1..2*n]});
    A21:=List(eMat{[n+1..2*n]}, x->x{[1..n]});
    A22:=List(eMat{[n+1..2*n]}, x->x{[n+1..2*n]});
    Amat:=A11;
    Bmat:=A12;
    if A21 <> -eProd*Bmat then
      Error("Conceptual error 1");
    fi;
    if A22 <> Amat + eSum*Bmat then
      Error("Conceptual error 2");
    fi;
    eDelta:=eSum*eSum - 4*eProd;
    alpha:=(eSum + Sqrt(eDelta))/2;
    eMatRes:=Amat + alpha*Bmat;
    TheDet:=DeterminantMat(eMatRes);
    if TheDet=1 then
      return true;
    fi;
    return false;
  end;
  return rec(Basis:=TheBasis, 
             SuperMat:=TheSuperMat,
             ScalProdMatrix:=GetScalProdMatrix(TheBasis, TheSuperMat), 
             ListComm:=[Imultiplication], 
             IsInSL:=IsInSL, IsInGL:=IsInGL,
             TrivialFilter:=TrivialFilter, 
             PtWiseStab:=Group([IdentityMat(2*n)]),
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
             ShortestFunction:=ShortestVectorDutourVersion);
end;




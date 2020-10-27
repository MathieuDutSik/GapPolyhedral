MINK_PreGetListIrredundant:=function()
  local TheList;
  TheList:=[
[1,1,0,0,0,0,0],
[1,1,1,0,0,0,0],
[1,1,1,1,0,0,0],
[1,1,1,1,1,0,0],
[2,1,1,1,1,0,0],

[1,1,1,1,1,1,0],
[2,1,1,1,1,1,0],
[2,2,1,1,1,1,0],
#[3,2,1,1,1,1,0],

[1,1,1,1,1,1,1],
[2,1,1,1,1,1,1],
[3,1,1,1,1,1,1],
[2,2,1,1,1,1,1],
[3,2,1,1,1,1,1],
[2,2,2,1,1,1,1],
[3,2,2,1,1,1,1],
[4,2,2,1,1,1,1],
[3,3,2,1,1,1,1],
[4,3,2,1,1,1,1],
[3,2,2,2,1,1,1],
[4,3,2,2,1,1,1]];
  return TheList;
end;
MINK_GetListIrredundant:=function(n)
  local TheList, RefDim, eCase, ListReturn, eCase1, eCase2, eNorm;
  TheList:=MINK_PreGetListIrredundant();
  RefDim:=Length(TheList[1]);
  if n>RefDim then
    Error("Sorry, the list stops at dimension ", RefDim);
  fi;
  ListReturn:=[];
  for eCase in TheList
  do
    if RefDim>n then
      eCase1:=eCase{[1..n]};
      eCase2:=eCase{[n+1..RefDim]};
      eNorm:=eCase2*eCase2;
      if eNorm=0 then
        Add(ListReturn, eCase1);
      fi;
    else
      Add(ListReturn, eCase);
    fi;
  od;
  return ListReturn;
end;

MINK_VectorGCD:=function(eVect)
  local TheGcd, iVect;
  TheGcd:=eVect[1];
  for iVect in [2..Length(eVect)]
  do
    TheGcd:=GcdInt(TheGcd, eVect[iVect]);
  od;
  return AbsInt(TheGcd);
end;



MINK_GetListInequalitiesMd:=function(n)
  local TheList, GRP, ListReturn1, ListReturn2, eVect, pCol, iCol, BSet, eSol, fVect, TheAntiGroup, ListPartial, ListPartial2, O, ListVectorPairs, V1, V2, ListGCDidx, i, TheGcd;
  TheList:=MINK_GetListIrredundant(n);
  GRP:=SymmetricGroup(n);
  ListReturn1:=[];
  ListReturn2:=[];
  for eVect in TheList
  do
    pCol:=0;
    for iCol in [1..n]
    do
      if eVect[iCol]<>0 then
        pCol:=pCol+1;
      fi;
    od;
    BSet:=BuildSet(pCol, [1,-1]);
    TheAntiGroup:=Group([-IdentityMat(n)]);
    ListPartial:=[];
    for eSol in BSet
    do
      fVect:=[];
      for iCol in [1..pCol]
      do
        Add(fVect, eSol[iCol]*eVect[iCol]);
      od;
      Append(fVect, ListWithIdenticalEntries(n-pCol,0));
      Add(ListPartial, fVect);
    od;
    O:=Orbits(TheAntiGroup, ListPartial);
    ListPartial2:=List(O, x->x[1]);
    Append(ListReturn1, ListPartial2);
    ListPartial:=[];
    for fVect in ListPartial2
    do
      Append(ListPartial, Orbit(GRP, fVect, Permuted));
    od;
    O:=Orbits(TheAntiGroup, ListPartial);
    ListPartial2:=List(O, x->x[1]);
    Append(ListReturn2, ListPartial2);
  od;
  ListVectorPairs:=[];
  for i in [1..n-1]
  do
    V1:=ListWithIdenticalEntries(n,0);
    V1[i]:=1;
    V2:=ListWithIdenticalEntries(n,0);
    V2[i+1]:=1;
    Add(ListVectorPairs, rec(Plus:=V1, Minus:=V2));
  od;
  for eVect in ListReturn2
  do
    ListGCDidx:=[];
    for i in [1..n]
    do
      TheGcd:=MINK_VectorGCD(eVect{[i..n]});
      if TheGcd=1 then
        Add(ListGCDidx, i);
      fi;
    od;
    V1:=ListWithIdenticalEntries(n,0);
    V1[Maximum(ListGCDidx)]:=1;
    Add(ListVectorPairs, rec(Plus:=V1, Minus:=eVect));
  od;
  return rec(ListReturn1:=ListReturn1, ListReturn2:=ListReturn2, ListVectorPairs:=ListVectorPairs);
end;

MINK_AddFirstZero:=function(eVect)
  return Concatenation([0], eVect);
end;





MINK_GetDefiningInequalitiesMd:=function(n)
  local h, ListPairs, ListMatrices, ListSymbol, TheSymmMat, ListIneq, ListIneqBis, ePair, V1, V2, eVect, ListScalVect, TheScal, fVect, i, eMat, IsItCanonicalVector, idx, idx1, idx2, ListMatrixTransform, TheMatTransform, GetPolyhedralTesselation, FuncDoRetraction;
  h:=n*(n+1)/2;
  ListPairs:=MINK_GetListInequalitiesMd(n).ListVectorPairs;
  ListMatrices:=[];
  ListSymbol:=[];
  IsItCanonicalVector:=function(eVect)
    local ListIdx;
    ListIdx:=Filtered([1..n], x->eVect[x]<>0);
    if Length(ListIdx)<>1 then
      return false;
    fi;
    return ListIdx[1];
  end;
  ListMatrixTransform:=[];
  for ePair in ListPairs
  do
    V1:=ePair.Plus;
    V2:=ePair.Minus;
    Print("V1=", V1, " V2=", V2, "\n");
    TheSymmMat:=TransposedMat([V2])*[V2]-TransposedMat([V1])*[V1];
    Add(ListMatrices, TheSymmMat);
    Add(ListSymbol, ePair);
    idx2:=IsItCanonicalVector(V2);
    if idx2<>false then
      idx1:=IsItCanonicalVector(V1);
      TheMatTransform:=NullMat(n,n);
      for idx in [1..n]
      do
        if idx<>idx1 and idx<>idx2 then
          TheMatTransform[idx][idx]:=1;
        fi;
      od;
      TheMatTransform[idx1][idx2]:=1;
      TheMatTransform[idx2][idx1]:=1;
    else
      idx1:=IsItCanonicalVector(V1);
      TheMatTransform:=[];
      for idx in [1..n]
      do
        if idx=idx1 then
          Add(TheMatTransform, V2);
        else
          eVect:=ListWithIdenticalEntries(n,0);
          eVect[idx]:=1;
          Add(TheMatTransform, eVect);
        fi;
      od;
      if AbsInt(DeterminantMat(TheMatTransform))<>1 then
        Print("We need to use more clever techniques for finding\n");
        Print("The equivalences\n");
        Error("Please program");
      fi;
    fi;
    Add(ListMatrixTransform, TheMatTransform);
  od;
  Print("We have the matrices of equivalences\n");
  ListIneq:=List(ListMatrices, x->MINK_AddFirstZero(SymmetricMatrixToVector(x)));
  ListIneq:=[];
  ListIneqBis:=[];
  for eMat in ListMatrices
  do
    ListScalVect:=[];
    for i in [1..h]
    do
      fVect:=ListWithIdenticalEntries(h,0);
      fVect[i]:=1;
      TheSymmMat:=VectorToSymmetricMatrix(fVect, n);
      TheScal:=Trace(TheSymmMat*eMat);
      Add(ListScalVect, TheScal);
    od;
    Add(ListIneqBis, ListScalVect);
  od;
  GetPolyhedralTesselation:=function()
    local ListMatrStabGens, i, eMat, TheGen, j, fVect, TheSymmMat, TheImgSymmMat, TheMatrStab, ListPos, nbIneqRed, ListIneqRed, ListMatrGens, eGen, eMatrCongr, eList, StabPerm, O, ListAdj, eO, idx, idx2, eIneq, eSymbol, eTransMat, eAdj, PolyhedralTesselation;
    ListMatrStabGens:=[];
    for i in [1..n-1]
    do
      eMat:=IdentityMat(n);
      eMat[i][i]:=-1;
      TheGen:=TRS_SymmRep(TransposedMat(eMat));
      Add(ListMatrStabGens, TheGen);
    od;
    TheMatrStab:=Group(ListMatrStabGens);
    ListPos:=RedundancyCheck(ListIneqBis);
    nbIneqRed:=Length(ListPos);
    Print("|ListIneqBis|=", Length(ListIneqBis), " |ListPos|=", nbIneqRed, "\n");
    ListIneqRed:=ListIneqBis{ListPos};
    ListMatrGens:=[];
    for eGen in ListMatrStabGens
    do
      eMatrCongr:=CongrMap(eGen);
      eList:=List(ListIneqRed, x->Position(ListIneqRed, x*eMatrCongr));
      Add(ListMatrGens, PermList(eList));
    od;
    StabPerm:=Group(ListMatrGens);
    O:=Orbits(StabPerm, [1..nbIneqRed], OnPoints);
    ListAdj:=[];
    for eO in O
    do
      idx:=eO[1];
      idx2:=ListPos[idx];
      eIneq:=ListIneqRed[idx];
      eMat:=Inverse(ListMatrixTransform[idx2]);
      eSymbol:=ListSymbol[idx2];
      eTransMat:=TRS_SymmRep(TransposedMat(eMat));
      eAdj:=rec(iRecord:=1, eEquiv:=eTransMat, eFac:=eIneq, eSymbol:=eSymbol);
      Add(ListAdj, eAdj);
    od;
    PolyhedralTesselation:=[rec(MatrixStab:=TheMatrStab, ListAdj:=ListAdj)];
    return PolyhedralTesselation;
  end;
  FuncDoRetraction:=function(eVect)
    local eMat;
    eMat:=VectorToSymmetricMatrix(eVect, n);
    if RankMat(eMat) < n then
      return true;
    else
      return false;
    fi;
  end;
  return rec(ListIneq:=ListIneq,
             ListIneqBis:=ListIneqBis,
             ListMatrices:=ListMatrices,
             ListSymbol:=ListSymbol,
             ListMatrixTransform:=ListMatrixTransform, 
             FuncDoRetraction:=FuncDoRetraction, 
             GetPolyhedralTesselation:=GetPolyhedralTesselation);
end;


MINK_GetDefiningInequalitiesMdPlus:=function(n)
  local h, ListPairs, ListIneq, ePair, V1, V2, i, TheSymmMat, eVect, ListSymbol, ListMatrices, ListIneqBis, eMat, ListScalVect, fVect, TheScal;
  h:=n*(n+1)/2;
  ListPairs:=MINK_GetListInequalitiesMd(n).ListVectorPairs;
  ListMatrices:=[];
  ListSymbol:=[];
  for ePair in ListPairs
  do
    V1:=ePair.Plus;
    V2:=ePair.Minus;
    Print("V1=", V1, " V2=", V2, "\n");
    TheSymmMat:=TransposedMat([V2])*[V2]-TransposedMat([V1])*[V1];
    Add(ListMatrices, TheSymmMat);
    Add(ListSymbol, ePair);
  od;
  for i in [1..n-1]
  do
    TheSymmMat:=NullMat(n,n);
    TheSymmMat[i][i+1]:=1;
    TheSymmMat[i+1][i]:=1;
    Add(ListMatrices, TheSymmMat);
    Add(ListSymbol, rec(Stat:="positivity", eAr:=[i,i+1]));
  od;
  ListIneq:=List(ListMatrices, x->MINK_AddFirstZero(SymmetricMatrixToVector(x)));
  ListIneqBis:=[];
  for eMat in ListMatrices
  do
    ListScalVect:=[];
    for i in [1..h]
    do
      fVect:=ListWithIdenticalEntries(h,0);
      fVect[i]:=1;
      TheSymmMat:=VectorToSymmetricMatrix(fVect, n);
      TheScal:=Trace(TheSymmMat*eMat);
      Add(ListScalVect, TheScal);
    od;
    Add(ListIneqBis, ListScalVect);
  od;
  return rec(ListIneq:=ListIneq, ListIneqBis:=ListIneqBis, ListMatrices:=ListMatrices, ListSymbol:=ListSymbol);
end;





MINK_GetRaysDirectMethod:=function(n)
  local ListPairs, ListIneq, ePair, V1, V2, EXT, ListMat, FuncInsert, eEXT, TheM, i, j, eVect, len;
  ListPairs:=MINK_GetListInequalitiesMd(n).ListVectorPairs;
  ListIneq:=[];
  for ePair in ListPairs
  do
    V1:=ePair.Plus;
    V2:=ePair.Minus;
    eVect:=SymmetricMatrixToVector(TransposedMat([V2])*[V2]-TransposedMat([V1])*[V1]);
    Add(ListIneq, MINK_AddFirstZero(eVect));
  od;
  EXT:=DualDescription(ListIneq);
  ListMat:=[];
  FuncInsert:=function(TheMat)
    local eMat, test;
    for eMat in ListMat
    do
      test:=ArithmeticEquivalenceMatrixFamily_Souvignier("", [eMat], [], [TheMat], []);
      if test<>false then
        return;
      fi;
    od;
    Add(ListMat, TheMat);
  end;
  for eEXT in EXT
  do
    len:=Length(eEXT);
    TheM:=VectorToSymmetricMatrix(eEXT{[2..len]}, n);
    for i in [1..n]
    do
      for j in [1..n]
      do
        if i<>j then
          TheM[i][j]:=TheM[i][j]/2;
        fi;
      od;
    od;
    if IsPositiveSymmetricMatrix(TheM)=false then
      Error("There is a logical problem");
    fi;
    if RankMat(TheM)=n then
      FuncInsert(RemoveFractionMatrix(TheM));
    fi;
  od;
  return rec(ListIneq:=ListIneq, EXT:=EXT, ListMat:=ListMat);
end;

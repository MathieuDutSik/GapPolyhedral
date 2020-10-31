FilePEV:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"GetPEV_forRead");



ConvertNumberToBinary:=function(eNumber)
  local TheRet, idx, eNumberWork, eRes;
  TheRet:=[];
  idx:=1;
  eNumberWork:=eNumber;
  while(true)
  do
    if eNumberWork=0 then
      return TheRet;
    fi;
    eRes:=eNumberWork mod 2;
    if eRes=1 then
      Add(TheRet, idx);
    fi;
    idx:=idx+1;
    eNumberWork:=(eNumberWork - eRes)/2;
  od;
end;



ConvertBinaryToNumber:=function(eSet)
  local eNb, len, i;
  eNb:=0;
  len:=Maximum(eSet);
  for i in [1..len]
  do
    if Position(eSet, i)<>fail then
      eNb:=eNb + 2^(i-1);
    fi;
  od;
  return eNb;
end;



# This is procedure for reading data set 
# from the Philippe Elbaz Vincent format
# See his database on
# http://www-fourier.ujf-grenoble.fr/~pev/PFPK/
GetPEV_DataSet:=function(ListSHV, eFile)
  local eFileOut, eList, ListCases, eEnt, eNumber, eIdx, eSHV, eSet, eCase;
  eFileOut:=Filename(POLYHEDRAL_tmpdir,"PEVout");
#  Print("eFile=", eFile, "\n");
  Exec(FilePEV, " ", eFile, " ", eFileOut);
  #
  eList:=ReadAsFunction(eFileOut)();
  ListCases:=[];
  for eEnt in eList
  do
    eNumber:=eEnt[1];
    eIdx:=eEnt[2];
    eSHV:=ListSHV[eIdx];
    eSet:=ConvertNumberToBinary(eNumber);
#    Print("eNumber=", eNumber, " eIdx=", eIdx, " eSet=", eSet, "\n");
    eCase:=eSHV{eSet};
    Add(ListCases, eCase);
  od;
  return ListCases;
end;



GetConfigurationVectorFromPFPK:=function(n, rank)
  local eDir, eFileSHV, ListSHV, TheCodim, eFile, ListFamily, TestFamily, eFileRed1, eFileRed2, eFamily;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/PFPK")[1];
  eFileRed1:=Concatenation("minvecs_", String(n), ".gap");
  eFileSHV:=Filename(eDir, eFileRed1);
  ListSHV:=ReadAsFunction(eFileSHV)();
  TheCodim:=n*(n-1)/2 - (rank - n);
  eFileRed2:=Concatenation("database/GL", String(n), "/skeleton/GL", String(n), "SKELcodim", String(TheCodim));
  eFile:=Filename(eDir, eFileRed2);
  ListFamily:=GetPEV_DataSet(ListSHV, eFile);
  TestFamily:=function(eFam)
    local ListVect;
    ListVect:=List(eFam, x->SymmetricMatrixToVector(TransposedMat([x]) * [x]));
    return RankMat(ListVect) = rank;
  end;
  for eFamily in ListFamily
  do
    if TestFamily(eFamily) = false then
      Error("Wrong rank");
    fi;
  od;
  return ListFamily;
end;



GetSubspace:=function(SHV)
  local n, ListEqua, eVect, SymMat1, SymMat2, H1, NSP, eSol, ListBasis, RetMat, i;
  n:=Length(SHV[1]);
  ListEqua:=[];
  for eVect in SHV
  do
    SymMat1:=TransposedMat([eVect])*[eVect];
    SymMat2:=TransposedMat([SHV[1]])*[SHV[1]];
    H1:=SymmetricMatrixToVector(SymMat1-SymMat2);
    Add(ListEqua, H1);
  od;
  NSP:=GetTransposeNullspaceMat(ListEqua);
  if Length(NSP)<>1 then
    Error("The vector configuration put as input is not perfect");
  fi;
  ListBasis:=[];
  for eSol in NSP
  do
    eSol:=NSP[1];
    RetMat:=VectorToSymmetricMatrix(eSol, n);
    for i in [1..n]
    do
      RetMat[i][i]:=2*RetMat[i][i];
    od;
    Add(ListBasis, RetMat);
  od;
  return ListBasis;
end;



GetAllPerfectForm:=function(n)
  local eDir, eFile;
  if n>8 then
    Error("Results are not known beyond dimension 8");
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/PerfectLattices")[1];
  eFile:=Filename(eDir,Concatenation("ListPerfDim", String(n)));
  return ReadAsFunction(eFile)();
end;



VOR_GetPerfectConeFromGramMat:=function(GramMat)
  local SHV, MatrGRP, nbRed, SHVred, EXT, eVect, eSymVect, ListPermGens, eGen, eList, PermGRP;
  SHV:=ShortestVectorDutourVersion(GramMat);
  MatrGRP:=ArithmeticAutomorphismGroup([GramMat]);
  nbRed:=Length(SHV)/2;
  SHVred:=List([1..nbRed], x->SHV[2*x-1]);
  EXT:=[];
  for eVect in SHVred
  do
    eSymVect:=SymmetricMatrixToVector(TransposedMat([eVect]) * [eVect]);
    Add(EXT, eSymVect);
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(MatrGRP)
  do
    eList:=List(SHVred, x->GetPositionAntipodal(SHVred, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  PermGRP:=Group(ListPermGens);
  return rec(EXT:=EXT, GRP:=PermGRP);
end;



GetCorrespondingPerfectForm:=function(SHV)
  local ListBasis, RetMat;
  ListBasis:=GetSubspace(SHV);
  if Length(ListBasis)<>1 then
    Error("The SHV configuration do not define a perfect object");
  fi;
  RetMat:=ListBasis[1];
  if RetMat[1][1]< 0 then
    return RemoveFractionMatrix(-RetMat);
  else
    return RemoveFractionMatrix(RetMat);
  fi;
end;



GetIrregularityInfoGeneral:=function(ListMat)
  local n, ListVect, rnk, TotalRnk, NSP, TotalBasis, ListSol, eRedMat, TheIndex, DeltaSimp;
  n:=Length(ListMat[1]);
  ListVect:=List(ListMat, SymmetricMatrixToVector);
  rnk:=RankMat(ListVect);
  TotalRnk:=n*(n+1)/2;
  if rnk=TotalRnk then
    TotalBasis:=IdentityMat(TotalRnk);
  else
    NSP:=NullspaceIntMat(TransposedMat(ListVect));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
  fi;
  ListSol:=List(ListVect, x->SolutionMat(TotalBasis, x));
  eRedMat:=BaseIntMat(ListSol);
  TheIndex:=AbsInt(DeterminantMat(eRedMat));
  DeltaSimp:=Length(ListMat) - rnk;
  return rec(TheIndex:=TheIndex, DeltaSimp:=DeltaSimp);
end;



# According to a basic results (indicated by K. Hulek)
# a point in the toric variety is smooth or depending on whether
# the set of corresponding vector in Sym2(Z) can be extended
# to a full basis of Sym2(Z)
GetIrregularityInformationSHV:=function(SHV)
  local n, nbPair, SHVred, ListMat, ListVect, rnk, TotalRnk, NSP, TotalBasis, ListSol, eRedMat, TheIndex, DeltaSimp;
  n:=Length(SHV[1]);
  nbPair:=Length(SHV)/2;
  SHVred:=List([1..nbPair], x->SHV[2*x-1]);
  ListMat:=List(SHVred, x->TransposedMat([x])*[x]);
  return GetIrregularityInfoGeneral(ListMat);
end;



GetIrregularityInformation:=function(eMat)
  local SHV;
  SHV:=ShortestVectorDutourVersion(eMat);
  return GetIrregularityInformationSHV(SHV);
end;



#
# See Ryshkov_S.S._Baranovskii_E.P._Classical_Methods_in_the_theory_of_Lattice_Packings.pdf
# on page 56
# First set of facets seems to be (after equivalence)
# (x1 + xi)^2 and (xi +- xj)^2
# It defines just one orbit.
# The second set is formed of facets of the form
# (x1 +- xi)^2 and (xi + epsilon(ij) xj)^2
# with epsilon(ij)=epsilon(ji) = +- 1.
# so this makes many different orbits.
LatticeDn_and_facets:=function(n)
  local ListRoot, eSet, i, j, eList, eVect, GetRay, GRPanti, ListRootAnti, ListRay, GetPositionAnti, GRPperm, ListPermGensAnti, eGen, ListSets, FuncInsertFacet, eGRA, pos, posN, posB, eRoot, GRPpermAnti, eSign, ListRootAntiBasis, TheBasis;
  ListRoot:=[];
  for eSet in Combinations([1..n],2)
  do
    i:=eSet[1];
    j:=eSet[2];
    for eList in BuildSet(2, [-1,1])
    do
      eVect:=ListWithIdenticalEntries(n,0);
      eVect[i]:=eList[1];
      eVect[j]:=eList[2];
      Add(ListRoot, eVect);
    od;
  od;
  TheBasis:=GetZbasis(ListRoot);
  GetRay:=function(eVect)
    return SymmetricMatrixToVector(TransposedMat([eVect])*[eVect]);
  end;
  GRPanti:=Group([-IdentityMat(n)]);
  ListRootAnti:=List(Orbits(GRPanti, ListRoot, OnPoints), x->x[1]);
  ListRootAntiBasis:=List(ListRootAnti, x->SolutionMat(TheBasis, x));
  ListRay:=List(ListRootAntiBasis, GetRay);
  GetPositionAnti:=function(eRoot)
    local pos;
    pos:=Position(ListRootAnti, eRoot);
    if pos<>fail then
      return pos;
    fi;
    return Position(ListRootAnti, -eRoot);
  end;
  GRPperm:=LinPolytope_Automorphism(ListRoot);
  ListPermGensAnti:=[];
  for eGen in GeneratorsOfGroup(GRPperm)
  do
    eList:=[];
    for eRoot in ListRootAnti
    do
      pos:=Position(ListRoot, eRoot);
      posN:=OnPoints(pos, eGen);
      posB:=GetPositionAnti(ListRoot[posN]);
      Add(eList, posB);
    od;
    Add(ListPermGensAnti, PermList(eList));
  od;
  GRPpermAnti:=Group(ListPermGensAnti);
  #
  ListSets:=[];
  FuncInsertFacet:=function(eSet)
    local fSet;
    for fSet in ListSets
    do
      if RepresentativeAction(GRPpermAnti, eSet, fSet, OnSets)<>fail then
        return;
      fi;
    od;
    Add(ListSets, eSet);
  end;
  # The big wall
  eList:=[];
  for i in [1..n-1]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    eVect[n]:=1;
    Add(eList, GetPositionAnti(eVect));
  od;
  for i in [1..n-2]
  do
    for j in [i+1..n-1]
    do
      eVect:=ListWithIdenticalEntries(n,0);
      eVect[i]:=1;
      eVect[j]:=1;
      Add(eList, GetPositionAnti(eVect));
      eVect:=ListWithIdenticalEntries(n,0);
      eVect[i]:=-1;
      eVect[j]:=1;
      Add(eList, GetPositionAnti(eVect));
    od;
  od;
  eSet:=Set(eList);
  FuncInsertFacet(eSet);
  # The small walls
  for eGRA in GetIsomorphismTypeGraph(n-1)
  do
    eList:=[];
    for i in [1..n-1]
    do
      eVect:=ListWithIdenticalEntries(n,0);
      eVect[i]:=1;
      eVect[n]:=1;
      Add(eList, GetPositionAnti(eVect));
      eVect:=ListWithIdenticalEntries(n,0);
      eVect[i]:=-1;
      eVect[n]:=1;
      Add(eList, GetPositionAnti(eVect));
    od;
    for i in [1..n-2]
    do
      for j in [i+1..n-1]
      do
        pos:=Position(eGRA[i], j);
        if pos=fail then
          eSign:=1;
        else
          eSign:=-1;
        fi;
        eVect:=ListWithIdenticalEntries(n,0);
        eVect[i]:=1;
        eVect[j]:=eSign;
        Add(eList, GetPositionAnti(eVect));
      od;
    od;
    eSet:=Set(eList);
    FuncInsertFacet(eSet);
  od;
  return rec(ListRoot:=ListRoot,
             ListRootAnti:=ListRootAnti,
             ListRootAntiBasis:=ListRootAntiBasis,
             GRPperm:=GRPperm,
             GRPpermAnti:=GRPpermAnti,
             ListRay:=ListRay,
             ListSets:=ListSets);
end;



GetEutacticRealization:=function(ListVect)
  local n, ListVectTot, HMat, eVect, eInvMat, ListNorm, RetMat;
  n:=Length(ListVect[1]);
  ListVectTot:=Set(Concatenation(ListVect, -ListVect));
  HMat:=NullMat(n,n);
  for eVect in ListVect
  do
    HMat:=HMat + TransposedMat([eVect])*[eVect];
  od;
  eInvMat:=Inverse(HMat);
  ListNorm:=List(ListVect, x->x*eInvMat*x);
  if Length(Set(ListNorm))<>1 then
    return false;
  fi;
  RetMat:=eInvMat/ListNorm[1];
  if Set(ShortestVectorDutourVersion(RetMat))<>ListVectTot then
    return false;
  fi;
  return RetMat;
end;



CanonicalizeVectForPerfect:=function(eVect)
  local eVal;
  if eVect*eVect=0 then
    return eVect;
  fi;
  eVal:=First(eVect, x->x<>0);
  if eVal> 0 then
    return eVect;
  else
    return -eVect;
  fi;
end;



SearchIntersectionConePositiveDefinite:=function(eMat, ListDir)
  local n, SHVdef, ListIneq, rnk, ListMatDefIneq, nbMat, eIneqAff, GetIneq, FuncInsertVector, FuncInsertVectorRnk, eLev, ToBeMinimized, nbIter, TheLP, eVectEmb, eMatrixSol, eEnt, NSP, NewVect, eVect, SetIneq;
  n:=Length(eMat);
  SHVdef:=[];
  ListIneq:=[];
  rnk:=0;
  ListMatDefIneq:=Concatenation([eMat], ListDir);
  nbMat:=Length(ListMatDefIneq);
  eIneqAff:=ListWithIdenticalEntries(1+nbMat,0);
  eIneqAff[2]:=1;
  eIneqAff[1]:=-1;
  Add(ListIneq, eIneqAff);
  rnk:=rnk+1;
  GetIneq:=function(eVect)
    return Concatenation([-1], List(ListMatDefIneq, x->eVect*x*eVect));
  end;
  FuncInsertVector:=function(eVect)
    local eLine;
    Add(SHVdef, eVect);
    eLine:=GetIneq(eVect);
    Add(ListIneq, eLine);
  end;
  FuncInsertVectorRnk:=function(eVect)
    local eLine;
    eLine:=GetIneq(eVect);
    if RankMat(Concatenation(ListIneq, [eLine])) > rnk then
      FuncInsertVector(eVect);
      rnk:=rnk+1;
    fi;
  end;
  for eVect in IdentityMat(n)
  do
    FuncInsertVector(eVect);
  od;
  eLev:=1;
  while(true)
  do
    for eVect in BuildSet(n, [-eLev..eLev])
    do
      FuncInsertVectorRnk(eVect);
    od;
#    Print("RankMat(ListIneq)=", RankMat(ListIneq), "\n");
    if RankMat(ListIneq)=nbMat+1 then
      break;
    fi;
    eLev:=eLev+1;
  od;
  ToBeMinimized:=ListWithIdenticalEntries(1+nbMat,0);
  ToBeMinimized[2]:=1;
  nbIter:=0;
  while(true)
  do
    SetIneq:=Set(ListIneq);
    TheLP:=LinearProgramming(SetIneq, ToBeMinimized);
    if IsBound(TheLP.primal_solution)=false then
      return rec(HaveSolution:=false);
    fi;
    eVectEmb:=ListWithIdenticalEntries(nbMat,0);
    eMatrixSol:=NullMat(n,n);
    for eEnt in TheLP.primal_solution
    do
      eVectEmb[eEnt[1]]:=eEnt[2];
      eMatrixSol:=eMatrixSol + eEnt[2]*ListMatDefIneq[eEnt[1]];
    od;
    eMatrixSol:=eMatrixSol/eVectEmb[1];
    if IsPositiveDefiniteSymmetricMatrix(eMatrixSol) then
      return rec(HaveSolution:=true, eMatrixSol:=eMatrixSol);
    else
      if RankMat(eMatrixSol)<n then
        NSP:=NullspaceMat(eMatrixSol);
        NewVect:=RemoveFraction(NSP[1]);
        Print("NSP NewVect=", NewVect, "\n");
        FuncInsertVector(NewVect);
      else
        NewVect:=EigenvalueFindNegativeVect(eMatrixSol);
#        Print("EIG NewVect=", NewVect, "\n");
        FuncInsertVector(NewVect);
      fi;
    fi;
  od;
end;





IsPerfectLattice:=function(GramMat)
  local n, SHV, ListEqua;
  n:=Length(GramMat);
  SHV:=ShortestVectorDutourVersion(GramMat);
  return Length(GetRankBasisPolytope(SHV))=0;
#  ListEqua:=List(SHV, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
#  return RankMat(ListEqua)=n*(n+1)/2;
end;



FindNegativeVector:=function(TheGram)
  local n, TheDiag, RedMat, idx, eVect, fVect;
  if IsPositiveSymmetricMatrix(TheGram)=true then
    Error("We cannot find a zero vector for a positive definite matrix");
  fi;
  n:=Length(TheGram);
  TheDiag:=DiagonalizeSymmetricMatrix(TheGram);
  RedMat:=TheDiag.RedMat;
  idx:=First([1..n], x->RedMat[x][x]<0);
  eVect:=ListWithIdenticalEntries(n,0);
  eVect[idx]:=1;
  fVect:=eVect*TheDiag.Transform;
  if fVect*TheGram*fVect >= 0 then
    Error("We are wrong");
  fi;
  return RemoveFraction(fVect);
end;



GRAM_GetALowVector:=function(TheGram)
  local NSP, SHV;
  if IsPositiveSymmetricMatrix(TheGram)=false then
    return FindNegativeVector(TheGram);
  fi;
  if IsPositiveDefiniteSymmetricMatrix(TheGram)=false then
    NSP:=NullspaceMat(TheGram);
    return RemoveFraction(NSP[1]);
  fi;
  SHV:=ShortestVectorDutourVersion(TheGram);
  return SHV[1];
end;



#
#
# algorithm by A. Schuermann
# Computational geometry of positive definite quadratic forms
# polyhedral reduction theories, algorithms and applications,
# page 32.
# There is a correction to allow for the case that R + u R is
# the perfect form that we want.
DoFlipping_perfectform:=function(SHVgroups, TheSubset)
  local SHV, eGroup, n, TheGramPerf, MinPerf, ListSymm, eSol, FacetMat, i, TheLowVect, GramMatNew, SHVnew, eVectMin, TheLowerBound, TheUpperBound, TheGamma, rVal, qVal, eVectGamma, eMinGamma, GramMatGamma, SHVgamma, SHVlow, nLow, nUpp, GramMatLow, eMinUpp, SHVupp, GramMatUpp, TheVal;
  SHV:=[];
  for eGroup in SHVgroups
  do
    Append(SHV, eGroup);
  od;
  eVectMin:=SHV[1];
  n:=Length(eVectMin);
  TheGramPerf:=GetCorrespondingPerfectForm(SHV);
  MinPerf:=eVectMin*TheGramPerf*eVectMin;
  ListSymm:=List(SHVgroups, x->SymmetricMatrixToVector(TransposedMat([x[1]])*[x[1]]));
  eSol:=FindFacetInequality(ListSymm, TheSubset);
  FacetMat:=VectorToSymmetricMatrix(eSol, n);
  for i in [1..n]
  do
    FacetMat[i][i]:=2*FacetMat[i][i];
  od;
  TheLowerBound:=0;
  TheUpperBound:=1;
  while(true)
  do
    GramMatUpp:=TheGramPerf+TheUpperBound*FacetMat;
    if IsPositiveDefiniteSymmetricMatrix(GramMatUpp)=false then
      TheUpperBound:=(TheLowerBound+TheUpperBound)/2;
    else
      SHVupp:=ShortestVectorDutourVersion(GramMatUpp);
      eMinUpp:=SHVupp[1]*GramMatUpp*SHVupp[1];
      if eMinUpp=MinPerf then
        nLow:=TheUpperBound;
        nUpp:=2*TheUpperBound;
        TheLowerBound:=nLow;
        TheUpperBound:=nUpp;
      else
        break;
      fi;
    fi;
  od;
  while(true)
  do
    GramMatLow:=TheGramPerf+TheLowerBound*FacetMat;
    SHVlow:=ShortestVectorDutourVersion(GramMatLow);
    GramMatUpp:=TheGramPerf+TheUpperBound*FacetMat;
    SHVupp:=ShortestVectorDutourVersion(GramMatUpp);
    eMinUpp:=SHVupp[1]*GramMatUpp*SHVupp[1];
    if eMinUpp=MinPerf then
      return RemoveFractionMatrix(GramMatUpp);
    fi;
    if IsSubset(Set(SHV), Set(SHVlow))=false then
      break;
    fi;
    TheGamma:=(TheLowerBound + TheUpperBound)/2;
    GramMatGamma:=TheGramPerf+TheGamma*FacetMat;
    SHVgamma:=ShortestVectorDutourVersion(GramMatGamma);
    eVectGamma:=SHVgamma[1];
    eMinGamma:=eVectGamma*GramMatGamma*eVectGamma;
    if eMinGamma >= MinPerf then
      TheLowerBound:=TheGamma;
    else
      TheUpperBound:=TheGamma;
      for eVectGamma in SHVgamma
      do
        rVal:=eVectGamma*FacetMat*eVectGamma;
        qVal:=eVectGamma*TheGramPerf*eVectGamma;
        if rVal < 0 then
          TheVal:=(MinPerf - qVal)/rVal;
          TheUpperBound:=Minimum([TheUpperBound, TheVal]);
        fi;
      od;
    fi;
  od;
  return RemoveFractionMatrix(TheGramPerf+TheLowerBound*FacetMat);
end;





DoFlippingTspace_Kernel:=function(Qmat, ShortestFunction, IsAdmissible, SHV, Rmat)
  local eGroup, n, MinPerf, ListSymm, eSol, i, TheLowVect, GramMatNew, SHVnew, eVectMin, TheLowerBound, TheUpperBound, TheGamma, rVal, qVal, eVectGamma, eMinGamma, GramMatGamma, SHVgamma, SHVlow, nLow, nUpp, Qlow, eMinUpp, SHVupp, Qupp, TheVal, eMinLow, ListSHVupp, ListMinUpp, ListMinLow, ListUpperBound, ListLowerBound, ListMinGamma, ListSHVgamma, ListDiff, RetMat;
  if IsPositiveSymmetricMatrix(Rmat)=true then
    Print("The Rmat matrix is positive semidefinite\n");
    Error("This means that we are at a dead end");
  fi;
  eVectMin:=SHV[1];
  n:=Length(eVectMin);
  MinPerf:=eVectMin*Qmat*eVectMin;
  TheLowerBound:=0;
  TheUpperBound:=1;
  ListSHVupp:=[];
  ListMinUpp:=[];
  ListUpperBound:=[];
  ListLowerBound:=[];
  while(true)
  do
    Qupp:=Qmat+TheUpperBound*Rmat;
    if IsAdmissible(Qupp)=false then
      TheUpperBound:=(TheLowerBound+TheUpperBound)/2;
    else
      SHVupp:=ShortestFunction(Qupp);
      eMinUpp:=SHVupp[1]*Qupp*SHVupp[1];
      Add(ListSHVupp, SHVupp);
      Add(ListMinUpp, eMinUpp);
      if eMinUpp=MinPerf then
        nLow:=TheUpperBound;
        nUpp:=2*TheUpperBound;
        TheLowerBound:=nLow;
        TheUpperBound:=nUpp;
      else
        break;
      fi;
    fi;
    Add(ListUpperBound, TheUpperBound);
    Add(ListLowerBound, TheLowerBound);
  od;
  #
  ListMinGamma:=[];
  ListUpperBound:=[];
  ListLowerBound:=[];
  ListMinLow:=[];
  ListMinUpp:=[];
  ListDiff:=[];
  ListSHVgamma:=[];
  while(true)
  do
    Qlow:=Qmat+TheLowerBound*Rmat;
    SHVlow:=ShortestFunction(Qlow);
    eMinLow:=SHVlow[1]*Qlow*SHVlow[1];
    Add(ListMinLow, eMinLow);
    #
    Qupp:=Qmat+TheUpperBound*Rmat;
    SHVupp:=ShortestFunction(Qupp);
    eMinUpp:=SHVupp[1]*Qupp*SHVupp[1];
    Add(ListMinUpp, eMinUpp);
    if eMinUpp=MinPerf then
      return RemoveFractionMatrix(Qupp);
    fi;
    if IsSubset(Set(SHV), Set(SHVlow))=false then
      break;
    fi;
    TheGamma:=(TheLowerBound + TheUpperBound)/2;
    GramMatGamma:=Qmat+TheGamma*Rmat;
    SHVgamma:=ShortestFunction(GramMatGamma);
    eVectGamma:=SHVgamma[1];
    eMinGamma:=eVectGamma*GramMatGamma*eVectGamma;
    Add(ListUpperBound, TheUpperBound);
    Add(ListLowerBound, TheLowerBound);
    Add(ListDiff, TheUpperBound - TheLowerBound);
    Add(ListSHVgamma, SHVgamma);
    Add(ListMinGamma, eMinGamma);
    if eMinGamma >= MinPerf then
      TheLowerBound:=TheGamma;
    else
      TheUpperBound:=TheGamma;
      for eVectGamma in SHVgamma
      do
        rVal:=eVectGamma*Rmat*eVectGamma;
        qVal:=eVectGamma*Qmat*eVectGamma;
        if rVal < 0 then
          TheVal:=(MinPerf - qVal)/rVal;
          TheUpperBound:=Minimum([TheUpperBound, TheVal]);
        fi;
      od;
    fi;
  od;
  RetMat:=RemoveFractionMatrix(Qmat+TheLowerBound*Rmat);
  return RetMat;
end;



GetCorrespondingPerfectFormTspace:=function(TheBasis, SHV)
  local n, DimSpace, TheMat, eMat, Bterm, eSol, RetMat, i;
  n:=Length(SHV[1]);
  DimSpace:=Length(TheBasis);
  TheMat:=[];
  for eMat in TheBasis
  do
    Add(TheMat, List(SHV, x->x*eMat*x));
  od;
  Bterm:=ListWithIdenticalEntries(Length(SHV), 1);
  eSol:=SolutionMat(TheMat, Bterm);
  RetMat:=NullMat(n,n);
  for i in [1..DimSpace]
  do
    RetMat:=RetMat+eSol[i]*TheBasis[i];
  od;
  return RemoveFractionMatrix(RetMat);
end;



DoFlippingTspace:=function(eCase, TheFormal, TheSubset)
  local n, DimSpace, TheGramPerf, eEXT, FacetMat, i, eVal, idx, eVectShort;
  n:=Length(eCase.Basis[1]);
  DimSpace:=Length(eCase.Basis);
  TheGramPerf:=GetCorrespondingPerfectFormTspace(eCase.Basis, TheFormal.SHV);
  eEXT:=FindFacetInequality(TheFormal.SetIneq, TheSubset);
  FacetMat:=NullMat(n,n);
  for i in [1..DimSpace]
  do
    FacetMat:=FacetMat+eEXT[i]*eCase.Basis[i];
  od;
  for eVal in TheSubset
  do
    idx:=TheFormal.ListRep[eVal];
    eVectShort:=TheFormal.SHV[idx];
    if eVectShort*FacetMat*eVectShort<>0 then
      Error("Inconsistency in DoFlippingTspace 1");
    fi;
  od;
  for eVal in Difference([1..Length(TheFormal.ListRep)], TheSubset)
  do
    idx:=TheFormal.ListRep[eVal];
    eVectShort:=TheFormal.SHV[idx];
    if eVectShort*FacetMat*eVectShort<=0 then
      Error("Inconsistency in DoFlippingTspace 2");
    fi;
  od;
  return DoFlippingTspace_Kernel(TheGramPerf, eCase.ShortestFunction, eCase.IsAdmissible, TheFormal.SHV, FacetMat);
end;



GetOnePerfectFormKernel:=function(eCase, GramMatIn)
  local n, DimSpace, ThePerfMat, SHV, TheMat, eMat, NSP, FacetMat, eZero, i, TheNewMat;
  n:=Length(eCase.Basis[1]);
  DimSpace:=Length(eCase.Basis);
  ThePerfMat:=GramMatIn;
#  Print("Entering GetOnePerfectForm\n");
  while(true)
  do
    SHV:=eCase.ShortestFunction(ThePerfMat);
    TheMat:=[];
    for eMat in eCase.Basis
    do
      Add(TheMat, List(SHV, x->x*eMat*x));
    od;
    NSP:=NullspaceMat(TheMat);
#    Print("|NSP|=", Length(NSP), "\n");
    if Length(NSP)=0 then
#      Print("All fine, we have the perfect form\n");
      return ThePerfMat;
    fi;
    FacetMat:=NullMat(n,n);
    eZero:=NSP[1];
    for i in [1..DimSpace]
    do
      FacetMat:=FacetMat+eZero[i]*eCase.Basis[i];
    od;
    TheNewMat:=DoFlippingTspace_Kernel(ThePerfMat, eCase.ShortestFunction, eCase.IsAdmissible, SHV, FacetMat);
    if TheNewMat=ThePerfMat then
      Error("Please debug from here");
    fi;
    ThePerfMat:=List(TheNewMat, x->x);
  od;
end;



TspaceFormalism:=function(eCase, SHV)
  local ListIneq, ListIneqRed, eVect, eLine, SetIneqRed, nbClass, ListGroups, ListRep, iIneq, ListPos, eIneq, TheQuadForm, iCanIdx, n, ListExpressionRays, BasisDualExpand, TheMat, ePos, TheMatExpand, eSol, BasisExpand, SetIneq, eInv, ListPermGens, eList, GRPshv, eSetSetOrbitShort, O, eGen;
  n:=Length(SHV[1]);
  ListIneq:=[];
  BasisExpand:=List(eCase.Basis, SymmetricMatrixToVector);
  for eVect in SHV
  do
    eLine:=List(eCase.Basis, x->eVect*x*eVect);
    Add(ListIneq, eLine);
  od;
  SetIneq:=Set(ListIneq);
  nbClass:=Length(SetIneq);
  ListGroups:=[];
  ListRep:=ListWithIdenticalEntries(nbClass, 0);
  ListExpressionRays:=[];
  eInv:=Inverse(eCase.ScalProdMatrix);
  for iIneq in [1..nbClass]
  do
    eIneq:=SetIneq[iIneq];
    ListPos:=Filtered([1..Length(SHV)], x->ListIneq[x]=eIneq);
    Add(ListGroups, ListPos);
    iCanIdx:=ListPos[1];
    eVect:=SHV[iCanIdx];
    ListRep[iIneq]:=iCanIdx;
    eSol:=eIneq*eInv;
    Add(ListExpressionRays, eSol);
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(eCase.SymmGrpPtWs)
  do
    eList:=List(SHV, x->Position(SHV, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  GRPshv:=Group(ListPermGens);
  O:=Orbits(GRPshv, [1..Length(SHV)], OnPoints);
  eSetSetOrbitShort:=Set(List(O, Set));
  return rec(SHV:=SHV, 
             ListGroups:=ListGroups,
             ListRep:=ListRep, 
             eSetSetOrbitShort:=eSetSetOrbitShort,
             ListExpressionRays:=ListExpressionRays, 
             SetIneq:=SetIneq);
end;



# LinearFunc is a linear function on the cone that can be expressed
# as a sum of vector evaluations on the cone.
TSPACE_GetContainingPerfectDomain:=function(TheGram, eCase, LinearFunc)
  local SHV, TheFormal, ListVect, TheRel, eSet;
  while(true)
  do
    SHV:=ShortestVectorDutourVersion(TheGram);
    TheFormal:=TspaceFormalism(eCase, SHV);
    ListVect:=Concatenation(TheFormal.SetIneq, [-LinearFunc]);
    TheRel:=SearchPositiveRelationSimple(ListVect);
    if TheRel<>false then
      return rec(TheGram:=TheGram, TheRel:=TheRel, TheFormal:=TheFormal);
    fi;
    eSet:=GetViolatedFacet(TheFormal.SetIneq, LinearFunc);
    TheGram:=DoFlippingTspace(eCase, TheFormal, eSet);
  od;
end;



GetOnePerfectForm:=function(eCase)
  local GramMatIn, TheGram;
  GramMatIn:=eCase.SuperMat;
  TheGram:=GetOnePerfectFormKernel(eCase, GramMatIn);
  if IsBound(eCase.ListExtRays)=false then
    return TheGram;
  fi;
  # Quite dubious code actually. But let us start with something
  Print("Debug at that stage\n");
  Print(NullMat(5));
  return TSPACE_GetContainingPerfectDomain(TheGram, eCase, eCase.SuperMat);
end;



EQUIV_TestSpaceStabilization:=function(TheBasis, eEquiv)
  local TheBasisExpand, eMatBasis, eSol;
  TheBasisExpand:=List(TheBasis, SymmetricMatrixToVector);
  for eMatBasis in TheBasis
  do
    eSol:=SolutionMat(TheBasisExpand, SymmetricMatrixToVector(eEquiv*eMatBasis*TransposedMat(eEquiv)));
    if eSol=fail then
      return false;
    fi;
  od;
  return true;
end;



EQUIV_TspaceExpression:=function(eCase, eEquiv)
  local eEquivTspace, TheBasisExpand, eMatBasis, eSol;
  eEquivTspace:=[];
  TheBasisExpand:=List(eCase.Basis, SymmetricMatrixToVector);
  for eMatBasis in eCase.Basis
  do
    eSol:=SolutionMat(TheBasisExpand, SymmetricMatrixToVector(eEquiv*eMatBasis*TransposedMat(eEquiv)));
    if eSol=fail then
      Print("We are not stabilizing the space!!!!!\n");
      Error("You need to program more");
    fi;
    Add(eEquivTspace, eSol);
  od;
  return eEquivTspace;
end;



EQUIV_TspaceExpressionDual:=function(eCase, eEquiv)
  local eMat;
  eMat:=EQUIV_TspaceExpression(eCase, eEquiv);
  return eCase.ScalProdMatrix*CongrMap(eMat)*Inverse(eCase.ScalProdMatrix);
end;



GetStabilizerTspace:=function(eCase, TheFormal, GramMat)
  local n, GRP, ListMatrGens, ListPermGens, eGen, eList, ListSets, eGroup, eSetSet, phi, TheStab, TheStabMatr, GRPpermSetIneq, GRPpermSHV, ListTspaceMatrGens, TheTspaceMatrStab, TheMat, eVect, eSol, ListPermGensSetIneq, eSet, TheBasisExpand, eMatBasis, eExprBasis, TheMatTrans, TheTspaceMatrStabTrans, eSolTrans, ThePreStab, eElt, FuncInsertElt, DimSpace, IsStabilizing, test, ListMatrGensStabTrans, SHVimg, fSet, eMatTrans, BigDiscalarMat, PreGRPpermSHV, GRPnew, ListGensNew, eMatrGen, ePermGen, eCommGen, ePerm, TestBelonging;
  n:=Length(eCase.Basis[1]);
  DimSpace:=Length(eCase.Basis);
  BigDiscalarMat:=GeneralWeightMatrix_FullDim_Commuting(GramMat, TheFormal.SHV, eCase.ListComm);
  PreGRPpermSHV:=AutomorphismWeightedDigraph(BigDiscalarMat);
  GRPpermSHV:=Stabilizer(PreGRPpermSHV, TheFormal.eSetSetOrbitShort, OnSetsSets);
  ListPermGens:=GeneratorsOfGroup(GRPpermSHV);
  ListMatrGens:=[];
  for ePermGen in ListPermGens
  do
    eMatrGen:=FindTransformation(TheFormal.SHV, TheFormal.SHV, ePermGen);
    for eCommGen in eCase.ListComm
    do
      if eMatrGen*eCommGen<>eCommGen*eMatrGen then
        Error("Commutation error in GetStabilizerTspace");
      fi;
    od;
    Add(ListMatrGens, eMatrGen);
  od;
  TestBelonging:=function(eGen)
    if EQUIV_TestSpaceStabilization(eCase.Basis, eGen)=false then
      return false;
    fi;
    return eCase.TheFilter(eGen);
  end;
  GRP:=Group(ListMatrGens);
  phi:=GroupHomomorphismByImagesNC(GRPpermSHV, GRP, ListPermGens, ListMatrGens);
  IsStabilizing:=true;
  for eGen in GeneratorsOfGroup(GRP)
  do
    test:=TestBelonging(eGen);
    if test=false then
      IsStabilizing:=false;
    fi;
  od;
  if IsStabilizing=false then
    ListGensNew:=[];
    GRPnew:=Group([IdentityMat(n)]);
    FuncInsertElt:=function(eElt)
      local test;
      test:=TestBelonging(eElt);
      if test=true then
        TheMat:=EQUIV_TspaceExpression(eCase, eElt);
        if eElt in GRPnew then
          return;
        fi;
        Add(ListGensNew, eElt);
        GRPnew:=PersoGroupMatrix(ListGensNew, n);
      fi;
    end;
    for eElt in GRP
    do
      FuncInsertElt(eElt);
    od;
    GRP:=PersoGroupMatrix(ListGensNew, n);
  fi;
  ListPermGensSetIneq:=[];
  ListTspaceMatrGens:=[];
  ListMatrGensStabTrans:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=[];
    for eSet in TheFormal.ListGroups
    do
      SHVimg:=List(TheFormal.SHV{eSet}, x->x*eGen);
      fSet:=Set(List(SHVimg, x->Position(TheFormal.SHV, x)));
      Add(eList, Position(TheFormal.ListGroups, fSet));
    od;
    ePerm:=PermList(eList);
    Add(ListPermGensSetIneq, ePerm);
    TheMat:=EQUIV_TspaceExpression(eCase, eGen);
    Add(ListTspaceMatrGens, TheMat);
    eMatTrans:=EQUIV_TspaceExpressionDual(eCase, eGen);
    Add(ListMatrGensStabTrans, eMatTrans);
  od;
  GRPpermSetIneq:=Group(ListPermGensSetIneq);
  TheTspaceMatrStabTrans:=Group(ListMatrGensStabTrans);
  TheTspaceMatrStab:=Group(ListTspaceMatrGens);
  return rec(TheTspaceMatrStab:=TheTspaceMatrStab, 
             TheTspaceMatrStabTrans:=TheTspaceMatrStabTrans,
             GRPpermSetIneq:=GRPpermSetIneq, 
             TheStabMatr:=GRP);
end;



TestEquivalenceTspace:=function(eCase, SHV1, GramMat1, SHV2, GramMat2)
  local eEquiv, eEquivInv, TheFormal1, TheFormal2, eList, ImageListGroups1, eGroup, eSList, eEquivTspace, eSol, GRPpermSHV2, eGen, eVal, eEquiv2, SetImageListGroups1, eEquivImg2, ListMatrGens2, phi2, GRP2, eVect, ListPermGens2, eEquivSought, eMatBasis, TheBasisExpand, TheImage, pos, eListGroupsTransformation, eEquivSoughtTrI, eEquivTspaceTrI, ThePreStab2, TheStab2, eCoset, eSetSet2, eRay, eCandEquiv, BigDiscalarMat1, BigDiscalarMat2, eCandPerm, eElt, PreGRPpermSHV2, eCandMatr, test, ImgESetSetOrbitShort1, ePerm, eMatrGen, ePermGen, eCommGen, eMatr, TestBelonging;
  TheFormal1:=TspaceFormalism(eCase, SHV1);
  TheFormal2:=TspaceFormalism(eCase, SHV2);
  BigDiscalarMat1:=GeneralWeightMatrix_FullDim_Commuting(GramMat1, SHV1, eCase.ListComm);
  BigDiscalarMat2:=GeneralWeightMatrix_FullDim_Commuting(GramMat2, SHV2, eCase.ListComm);
  test:=IsIsomorphicWeightDigraph(BigDiscalarMat1, BigDiscalarMat2);
  if test=false then
    return fail;
  fi;
  TestBelonging:=function(eGen)
    if EQUIV_TestSpaceStabilization(eCase.Basis, eGen)=false then
      return false;
    fi;
    return eCase.TheFilter(eGen);
  end;
  ePerm:=PermList(test);
  eMatr:=FindTransformation(TheFormal1.SHV, TheFormal2.SHV, ePerm);
  for eCommGen in eCase.ListComm
  do
    if eMatr*eCommGen<>eCommGen*eMatr then
      Error("Commutation error in TestEquivalenceTspace");
    fi;
  od;
  ImgESetSetOrbitShort1:=OnSetsSets(TheFormal1.eSetSetOrbitShort, ePerm);
  PreGRPpermSHV2:=AutomorphismWeightedDigraph(BigDiscalarMat2);
  test:=RepresentativeAction(PreGRPpermSHV2, ImgESetSetOrbitShort1, TheFormal2.eSetSetOrbitShort, OnSetsSets);
  if test=fail then
    return fail;
  fi;
  eCandPerm:=ePerm*test;
  eCandEquiv:=Inverse(FindTransformation(TheFormal1.SHV, TheFormal2.SHV, eCandPerm));
  if eCandEquiv*GramMat1*TransposedMat(eCandEquiv)<>GramMat2 then
    Error("We stop here for a break");
  fi;
  if TestBelonging(eCandEquiv)=true then
    eEquivTspace:=EQUIV_TspaceExpression(eCase, eCandEquiv);
    eEquivTspaceTrI:=EQUIV_TspaceExpressionDual(eCase, eCandEquiv);
    return rec(eEquiv:=eCandEquiv, 
               eEquivTspace:=eEquivTspace, 
               eEquivTspaceTrI:=eEquivTspaceTrI);
  fi;
  GRPpermSHV2:=Stabilizer(PreGRPpermSHV2, TheFormal2.eSetSetOrbitShort, OnSetsSets);
  #
  for eElt in GRPpermSHV2
  do
    eEquiv:=eCandPerm*eElt;
    eCandEquiv:=Inverse(FindTransformation(TheFormal1.SHV, TheFormal2.SHV, eEquiv));
    if TestBelonging(eCandEquiv)=true then
      eEquivTspace:=EQUIV_TspaceExpression(eCase, eCandEquiv);
      eEquivTspaceTrI:=EQUIV_TspaceExpressionDual(eCase, eCandEquiv);
      eList:=[];
      for eRay in TheFormal1.ListExpressionRays
      do
        pos:=Position(TheFormal2.ListExpressionRays, eRay*eEquivTspaceTrI);
        if pos=fail then
          Error("Please debug from that point only");
        fi;
        Add(eList, pos);
      od;
      return rec(eEquiv:=eCandEquiv, 
                 eEquivTspace:=eEquivTspace, 
                 eEquivTspaceTrI:=eEquivTspaceTrI);
    fi;
  od;
  return fail;
end;



GetActionOnShortest:=function(TheFormal, StabInfo)
  local ListPermGens, eGen, eList;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(StabInfo.TheTspaceMatrStabTrans)
  do
    eList:=List(TheFormal.ListExpressionRays, x->Position(TheFormal.ListExpressionRays, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  return Group(ListPermGens);
end;



# eCase:=rec(
#   Basis      a basis of matrices of the T-space considered
#   SuperMat   a positive definite matrix belonging to T (any one)
#   ListComm   All matrices M appearing in equivalence or stabilizer
#              will satisfy MP = PM for all P in ListComm
#   SymmGrpPtWs      the symmetry group of all matrices.
#              all elements M of the T-space will satisfy
#        U*M*TransposedMat(U)=M for U in TheGroup
#   ShortestFunction The function for computing shortest vectors
#                    Useful if we consider special kinds of vectors
#   [Optional if the case considered is a polyhedral cone]:
#     ListExtRays    list of extreme rays
#      ListFacets    list of facet defining inequalities
#     SymmGrpGlob    the matrix group preserving the considered polyhedral
#                    cone globally (necessarily finite, please fix the
#                    size in advance)
#
#   The relevant group G in that case will
#   ---contains TheGroup as subgroup
#   ---commute with all elements of ListComm
#   ---stabilize the T-space considered
#
#   Internally, we have two spaces to consider 
#   ---The Ryshkov space of the perfect forms (Direct)
#   ---The space of the perfect domain tesselation (Dual)
#   In Opgenorth, this is done by taking two different subspaces.
#   Here we choose to use only one subspace and (we hope) that by
#   using SuperMat for mapping that the dual space is embedded inside
#   of the positive semidefinite forms.
#
#   We provide in output
#   ---The list of perfect forms
#   ---A list of generators of G.
#   ---One record eRecIAIdirect for Isomorphism-Automorphism-Invarant
#   ---One record eRecIAIdual for Isomorphism-Automorphism-Invarant
#   ---Retraction functions that allows to know if a matrix is
#      positive definite.
Kernel_GetEnumerationPerfectForm:=function(eCaseGen2)
  local n, DimSpace, TheTesselation, FuncInsert, IsFinished, ListAdj, TheAdj, eFac, FlippedGram, iRecord, TheFormal, eOrb, PermGRP, GRP, GramMat, ListOrbit, SHV, nbRecord, DiscInfo, SingleOrbInfo, eGen, TheBasis, iOrb, nbOrb, FuncDoRetractionDual, FuncDoRetractionDirect, ListGenTotal, FuncIsomorphismDirect, FuncAutomorphismDirect, FuncInvariantDirect, eRecIAIdirect, FuncIsomorphismDual, FuncAutomorphismDual, FuncInvariantDual, eRecIAIdual, ScalProdMatrix, eScal, InvSuper, FuncDoRetractionDual_RankApproach, TheFormalDisc, SHVdisc, GRPpermSetIneq, TheBasisExpand, IsValidGram, RecExtRay, TotalNbPerfectCone;
  n:=Length(eCaseGen2.SuperMat[1]);
  TheTesselation:=[];
  ListGenTotal:=[];
  TheBasis:=eCaseGen2.Basis;
  DimSpace:=Length(TheBasis);
  TheBasisExpand:=List(TheBasis, SymmetricMatrixToVector);
  if IsBound(eCaseGen2.ListExtRays) then
    RecExtRay:=TSPACE_GetExtremeRayFunctions(eCaseGen2);
  fi;
  # We need a SHVdisc because it can happen that in a T-space
  # a family of shortest vector does not span the lattice, YES!
  FuncInsert:=function(TheNewGram)
    local iRecord, eRecord, eEquiv, SHV, SHVdisc, SHVrecord, eEquivInfo, eSol, GramMatExpand, eInv, extRaySig, test, eStabExtRay, OrbSiz, eEquivDirect;
    SHVdisc:=__ExtractInvariantZBasisShortVectorNoGroup(TheNewGram);
    eInv:=KernelGetInvariantGram(TheNewGram, SHVdisc);
    if IsBound(eCaseGen2.ListExtRays) then
      extRaySig:=RecExtRay.GetExtRaySignature(TheNewGram);
    fi;
    for iRecord in [1..Length(TheTesselation)]
    do
      eRecord:=TheTesselation[iRecord];
      if eRecord.eInv=eInv then
        if IsBound(eCaseGen2.ListExtRays)=false then
          SHVrecord:=eRecord.SHVdisc;
          eEquivInfo:=TestEquivalenceTspace(eCaseGen2, SHVrecord, eRecord.GramMat, SHVdisc, TheNewGram);
          if eEquivInfo<>fail then
            Add(ListGenTotal, eEquivInfo.eEquivTspace);
            return rec(iRecord:=iRecord, 
                       eEquivDirect:=eEquivInfo.eEquivTspace, 
                       eEquiv:=eEquivInfo.eEquivTspaceTrI);
          fi;
        else
          test:=RepresentativeAction(RecExtRay.PermGrpExtRays, extRaySig, eRecord.extRaySig, Permuted);
          if test<>fail then
            eEquivDirect:=PreImage(RecExtRay.phiExtRays, test);
            return rec(iRecord:=iRecord,
                       eEquivDirect:=eEquivDirect,
                       eEquiv:="unset");
          fi;
        fi;
      fi;
    od;
    SHV:=ShortestVectorDutourVersion(TheNewGram);
    GramMatExpand:=SymmetricMatrixToVector(TheNewGram);
    eSol:=SolutionMat(TheBasisExpand, GramMatExpand);
    eRecord:=rec(SHV:=SHV, 
                 eInv:=eInv, 
                 SHVdisc:=SHVdisc,
                 GramMat:=TheNewGram, 
                 eExpressionBasis:=eSol, 
                 Status:="NO");
    if IsBound(eCaseGen2.ListExtRays) then
      eRecord.extRaySig:=extRaySig;
      eStabExtRay:=Stabilizer(RecExtRay.PermGrpExtRays, extRaySig, Permuted);
      OrbSiz:=Order(RecExtRay.PermGrpExtRays) / Order(eStabExtRay);
      eRecord.OrbitSize:=OrbSiz;
      TotalNbPerfectCone:=TotalNbPerfectCone + OrbSiz;
    fi;
    Add(TheTesselation, eRecord);
    Print("Now we have ", Length(TheTesselation), " T-perfect forms\n");
    return rec(iRecord:=Length(TheTesselation), 
               eEquivDirect:=IdentityMat(DimSpace), 
               eEquiv:=IdentityMat(DimSpace));
  end;
#  This function apparently does not work for PGL3_EisInt
  FuncDoRetractionDual_RankApproach:=function(eInfo, EXTrelevant, eVect)
    local iOrbit, eSet, SystEquation, eVectShort, ListProd, i, eLine;
    iOrbit:=eInfo.iOrbitChosen;
    eSet:=List(EXTrelevant, x->Position(TheTesselation[iOrbit].EXT, x));
    SystEquation:=[];
    for eVectShort in TheTesselation[iOrbit].SHV{eSet}
    do
      ListProd:=List(TheBasis, x->eVectShort*x);
      for i in [1..n]
      do
        eLine:=List(ListProd, x->x[i]);
        Add(SystEquation, eLine);
      od;
    od;
    if RankMat(SystEquation)=DimSpace then
      return false;
    else
      return true;
    fi;
  end;
  FuncDoRetractionDirect:=function(eVect)
    local eMat, i;
    eMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      eMat:=eMat+eVect[i]*TheBasis[i];
    od;
    if RankMat(eMat) < n then
      return true;
    else
      return false;
    fi;
  end;
  FuncDoRetractionDual:=function(eInfo, EXTrelevant, eVect)
    return FuncDoRetractionDirect(eVect);
  end;
  IsValidGram:=function(CandGram)
    local SHVcand, TheFormalCand, FAC, testIntersection;
    if IsBound(eCaseGen2.ListExtRays)=false then
      return true;
    fi;
    SHVcand:=ShortestVectorDutourVersion(CandGram);
    TheFormalCand:=TspaceFormalism(eCaseGen2, SHVcand);
    FAC:=DualDescription(TheFormalCand.ListExpressionRays);
    testIntersection:=POLYDEC_HasConeNonVoidIntersection(eCaseGen2, FAC);
    return testIntersection;
  end;
  FuncInsert(GetOnePerfectForm(eCaseGen2));
  while(true)
  do
    IsFinished:=true;
    nbRecord:=Length(TheTesselation);
    for iRecord in [1..nbRecord]
    do
      if TheTesselation[iRecord].Status="NO" then
        TheTesselation[iRecord].Status:="YES";
        IsFinished:=false;
        SHVdisc:=TheTesselation[iRecord].SHVdisc;
        TheFormalDisc:=TspaceFormalism(eCaseGen2, SHVdisc);
        GramMat:=TheTesselation[iRecord].GramMat;
        SingleOrbInfo:=GetStabilizerTspace(eCaseGen2, TheFormalDisc, GramMat);
        Append(ListGenTotal, GeneratorsOfGroup(SingleOrbInfo.TheTspaceMatrStab));
        Print("|GRPpermSetIneq|=", Order(SingleOrbInfo.GRPpermSetIneq), "\n");
        SHV:=TheTesselation[iRecord].SHV;
        TheFormal:=TspaceFormalism(eCaseGen2, SHV);
        GRPpermSetIneq:=GetActionOnShortest(TheFormal, SingleOrbInfo);
        ListOrbit:=DualDescriptionStandard(TheFormal.SetIneq, GRPpermSetIneq);
        TheTesselation[iRecord].ListIneq:=TheFormal.SetIneq;
        TheTesselation[iRecord].PermGRP:=SingleOrbInfo.GRPpermSetIneq;
        TheTesselation[iRecord].MatrixStabDirect:=SingleOrbInfo.TheTspaceMatrStab;
        TheTesselation[iRecord].MatrixStab:=SingleOrbInfo.TheTspaceMatrStabTrans;
        ListAdj:=[];
        nbOrb:=Length(ListOrbit);
        for iOrb in [1..nbOrb]
        do
          eOrb:=ListOrbit[iOrb];
          FlippedGram:=DoFlippingTspace(eCaseGen2, TheFormal, eOrb);
          if IsValidGram(FlippedGram) then
            TheAdj:=FuncInsert(FlippedGram);
            eFac:=FindFacetInequality(TheFormal.ListExpressionRays, eOrb);
            Print("iOrb=", iOrb, "/", nbOrb, " orbit\n");
            TheAdj.eFac:=eFac;
            TheAdj.eOrb:=eOrb;
            TheAdj.FlippedGram:=FlippedGram;
            Add(ListAdj, TheAdj);
          fi;
        od;
        TheTesselation[iRecord].ListAdj:=ListAdj;
        TheTesselation[iRecord].EXT:=TheFormal.ListExpressionRays;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  Print("We find ", Length(TheTesselation), " perfect forms\n");
  FuncAutomorphismDirect:=function(eVect)
    local TheGramMat, i, SHV, TheFormal, StabInfo;
    TheGramMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat:=TheGramMat+eVect[i]*TheBasis[i];
    od;
    SHV:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
    TheFormal:=TspaceFormalism(eCaseGen2, SHV);
    StabInfo:=GetStabilizerTspace(eCaseGen2, TheFormal, TheGramMat);
    for eGen in GeneratorsOfGroup(StabInfo.TheTspaceMatrStab)
    do
      if eVect*eGen<>eVect then
        Error("We have an inconsistency in FuncAutomorphismDirect");
      fi;
    od;
    return StabInfo.TheTspaceMatrStab;
  end;
  FuncIsomorphismDirect:=function(eVect1, eVect2)
    local i, TheGramMat1, SHV1, TheFormal1, TheGramMat2, SHV2, TheFormal2, eEquivInfo;
    TheGramMat1:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat1:=TheGramMat1+eVect1[i]*eCaseGen2.Basis[i];
    od;
    SHV1:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat1);
    TheGramMat2:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat2:=TheGramMat2+eVect2[i]*TheBasis[i];
    od;
    SHV2:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat2);
    eEquivInfo:=TestEquivalenceTspace(eCaseGen2, SHV1, TheGramMat1, SHV2, TheGramMat2);
    if eEquivInfo<>fail then
      if eVect1*eEquivInfo.eEquivTspace<>eVect2 then
        Print("We have an inconsistency in FuncIsomorphismDirect\n");
        Print(NullMat(4));
      fi;
      return eEquivInfo.eEquivTspace;
    fi;
    return fail;
  end;
  FuncInvariantDirect:=function(eVect)
    local TheGramMat, i, SHV, eTool;
    TheGramMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat:=TheGramMat+eVect[i]*TheBasis[i];
    od;
    SHV:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
    return GeneralWeightMatrix_FullDim_Commuting_Invariant(TheGramMat, SHV, eCaseGen2.ListComm);
  end;
  eRecIAIdirect:=rec(FuncIsomorphism:=FuncIsomorphismDirect,
       FuncAutomorphism:=FuncAutomorphismDirect,
       FuncInvariant:=FuncInvariantDirect);
  FuncAutomorphismDual:=function(eVect)
    local TheGramMat, i, SHV, TheFormal, StabInfo, Hmat;
    TheGramMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat:=TheGramMat+eVect[i]*TheBasis[i];
    od;
    if IsPositiveSymmetricMatrix(TheGramMat)=false then
      Error("Error, the matrix should be positive semidefinite");
    fi;
    Hmat:=eCaseGen2.SuperMat*Inverse(TheGramMat)*eCaseGen2.SuperMat;
    SHV:=__ExtractInvariantZBasisShortVectorNoGroup(Hmat);
    TheFormal:=TspaceFormalism(eCaseGen2, SHV);
    StabInfo:=GetStabilizerTspace(eCaseGen2, TheFormal, Hmat);
    for eGen in GeneratorsOfGroup(StabInfo.TheTspaceMatrStabTrans)
    do
      if eVect*eGen<>eVect then
        Error("We have an inconsistency in FuncAutomorphismDual");
      fi;
    od;
    return StabInfo.TheTspaceMatrStabTrans;
  end;
  FuncIsomorphismDual:=function(eVect1, eVect2)
    local i, TheGramMat1, SHV1, TheFormal1, TheGramMat2, SHV2, TheFormal2, eEquivInfo, Hmat1, Hmat2;
    TheGramMat1:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat1:=TheGramMat1+eVect1[i]*TheBasis[i];
    od;
    if IsPositiveSymmetricMatrix(TheGramMat1)=false then
      Error("Error, the matrix should be positive semidefinite");
    fi;
    Hmat1:=eCaseGen2.SuperMat*Inverse(TheGramMat1)*eCaseGen2.SuperMat;
    SHV1:=__ExtractInvariantZBasisShortVectorNoGroup(Hmat1);
    #
    TheGramMat2:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat2:=TheGramMat2+eVect2[i]*TheBasis[i];
    od;
    if IsPositiveSymmetricMatrix(TheGramMat2)=false then
      Error("Error, the matrix should be positive semidefinite");
    fi;
    Hmat2:=eCaseGen2.SuperMat*Inverse(TheGramMat2)*eCaseGen2.SuperMat;
    SHV2:=__ExtractInvariantZBasisShortVectorNoGroup(Hmat2);
    eEquivInfo:=TestEquivalenceTspace(eCaseGen2, SHV1, Hmat1, SHV2, Hmat2);
    if eEquivInfo<>fail then
      if eVect1*eEquivInfo.eEquivTspaceTrI<>eVect2 then
        Print("We have an inconsistency in FuncIsomorphismDual\n");
        Print(NullMat(4));
      fi;
      return eEquivInfo.eEquivTspaceTrI;
    fi;
    return fail;
  end;
  FuncInvariantDual:=function(eVect)
    local TheGramMat, i, SHV, eTool, Hmat;
    TheGramMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      TheGramMat:=TheGramMat+eVect[i]*eCaseGen2.Basis[i];
    od;
    Hmat:=eCaseGen2.SuperMat*Inverse(TheGramMat)*eCaseGen2.SuperMat;
    SHV:=__ExtractInvariantZBasisShortVectorNoGroup(Hmat);
    return GeneralWeightMatrix_FullDim_Commuting_Invariant(Hmat, SHV, eCaseGen2.ListComm);
  end;
  eRecIAIdual:=rec(FuncIsomorphism:=FuncIsomorphismDual,
       FuncAutomorphism:=FuncAutomorphismDual,
       FuncInvariant:=FuncInvariantDual);
  return rec(eRecIAIdirect:=eRecIAIdirect,
             eRecIAIdual:=eRecIAIdual,
             TheTesselation:=TheTesselation,
             TotalNbPerfectCone:=TotalNbPerfectCone,
             ListGenTotal:=ListGenTotal,
             FuncDoRetractionDirect:=FuncDoRetractionDirect,
             FuncDoRetractionDual:=FuncDoRetractionDual);
end;



FindAllRyshkovNeighbors:=function(eCaseGen, TheGram)
  local SHVdisc, TheFormalDisc, SingleOrbInfo, SHV, TheFormal, GRPpermSetIneq, ListAdj, eOrb, TheAct, FlippedGram, Oadj, ListOrbit, TheSHV, eMin;
  SHVdisc:=__ExtractInvariantZBasisShortVectorNoGroup(TheGram);
  TheFormalDisc:=TspaceFormalism(eCaseGen, SHVdisc);
  SingleOrbInfo:=GetStabilizerTspace(eCaseGen, TheFormalDisc, TheGram);
  SHV:=ShortestVectorDutourVersion(TheGram);
  TheFormal:=TspaceFormalism(eCaseGen, SHV);
  GRPpermSetIneq:=GetActionOnShortest(TheFormal, SingleOrbInfo);
  ListOrbit:=DualDescriptionStandard(TheFormal.SetIneq, GRPpermSetIneq);
  ListAdj:=[];
  TheAct:=function(x, g)
    return g*x*TransposedMat(g);
  end;
  for eOrb in ListOrbit
  do
    FlippedGram:=DoFlippingTspace(eCaseGen, TheFormal, eOrb);
    TheSHV:=ShortestVectorDutourVersion(FlippedGram);
    eMin:=TheSHV[1]*FlippedGram*TheSHV[1];
    Oadj:=Orbit(SingleOrbInfo.TheStabMatr, FlippedGram, TheAct);
    Append(ListAdj, List(Oadj, x->x/eMin));
  od;
  return ListAdj;
end;



GetEnumerationPerfectFormGspace:=function(eCaseGen1)
  local ListGen, TheBasis, eCaseGen2, ScalProdMat;
  ListGen:=GeneratorsOfGroup(eCaseGen1.TheGroup);
  TheBasis:=InvariantFormDutourVersion(ListGen);
  ScalProdMat:=GetScalProdMatrix(TheBasis, eCaseGen1.SuperMat);
  eCaseGen2:=rec(SuperMat:=eCaseGen1.SuperMat,
                 ShortestFunction:=ShortestVectorDutourVersion,
                 IsAdmissible:=IsPositiveDefiniteSymmetricMatrix, 
                 Basis:=TheBasis,
                 ListComm:=[], 
                 ScalProdMatrix:=ScalProdMat,
                 SymmGrpPtWs:=eCaseGen1.TheGroup,
                 TheBasis:=TheBasis);
  return Kernel_GetEnumerationPerfectForm(eCaseGen2);
end;



ReverseProduct:=function(SymmMat)
  local n, ListNonZeroDiag, pos, eVect, eVal1, eVal2;
  n:=Length(SymmMat);
  ListNonZeroDiag:=Filtered([1..n], x->SymmMat[x][x]<>0);
  if ListNonZeroDiag=[] then
    return ListWithIdenticalEntries(n, 0);
  fi;
  pos:=ListNonZeroDiag[1];
  eVal1:=SymmMat[pos][pos];
  eVal2:=Sqrt(eVal1);
  if IsRat(eVal2)=false then
    Error("We have error by Sqrt, please provide right vector");
  fi;
  eVect:=SymmMat[pos]/eVal2;
  if TransposedMat([eVect])*[eVect]<>SymmMat then
    Error("We have error");
  fi;
  return eVect;
end;



RevTRS_SymmRep:=function(n, eBigMat)
  local ListPossibilities, i, eVect, eSymmMat, eVectMat, fVectMat, fSymmMat, fVect, ListSolution, fVect1, fVect2, fVectMat1, fVectMat2;
  if DeterminantMat(eBigMat)=0 then
    Error("The code requires invertibility");
  fi;
  ListPossibilities:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    eSymmMat:=TransposedMat([eVect])*[eVect];
    eVectMat:=SymmetricMatrixToVector(eSymmMat);
    fVectMat:=eVectMat*eBigMat;
    fSymmMat:=VectorToSymmetricMatrix(fVectMat, n);
    fVect:=ReverseProduct(fSymmMat);
    Add(ListPossibilities, fVect);
  od;
  ListSolution:=[ListPossibilities[1]];
  for i in [2..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[1]:=1;
    eVect[i]:=1;
    eSymmMat:=TransposedMat([eVect])*[eVect];
    eVectMat:=SymmetricMatrixToVector(eSymmMat);
    fVectMat:=eVectMat*eBigMat;
    fVect1:=ListPossibilities[1]+ListPossibilities[i];
    fVectMat1:=SymmetricMatrixToVector(TransposedMat([fVect1])*[fVect1]);
    fVect2:=ListPossibilities[1]-ListPossibilities[i];
    fVectMat2:=SymmetricMatrixToVector(TransposedMat([fVect2])*[fVect2]);
    if fVectMat1<>fVectMat and fVectMat2<>fVectMat then
      Print("The matrix eBigMat is NOT obtained as tensor product\n");
      Print("on the symmetric matrices\n");
      Error("Please correct");
    fi;
    if fVectMat1=fVectMat then
      Add(ListSolution, ListPossibilities[i]);
    else
      Add(ListSolution, -ListPossibilities[i]);
    fi;
  od;
  return ListSolution;
end;



TRS_SymmRep:=function(eGen)
  local n, eNewMat, i, eVect, eMat, nbDim;
  n:=Length(eGen);
  nbDim:=n*(n+1)/2;
  eNewMat:=[];
  for i in [1..nbDim]
  do
    eVect:=ListWithIdenticalEntries(nbDim, 0);
    eVect[i]:=1;
    eMat:=VectorToSymmetricMatrix(eVect, n);
    Add(eNewMat, SymmetricMatrixToVector(TransposedMat(eGen)*eMat*eGen));
  od;
  return eNewMat;
end;



ReverseBoundary:=function(n, TheBound)
  local TheNewListOrbitByRank, nbRank, iRank, nbOrbit, TheListOrbit, iOrbit, ListNewStabGens, eGen, TheNewStab, TheNewListElt, TheNewBound, NewSer, TheNewFuncSignatureDet, TheNewStabRot, ListNewStabGensRot, TheNewIdentityElt;
  nbRank:=Length(TheBound.ListOrbitByRank);
  TheNewListOrbitByRank:=[];
  Add(TheNewListOrbitByRank, TheBound.ListOrbitByRank[1]);
  for iRank in [2..nbRank]
  do
    nbOrbit:=Length(TheBound.ListOrbitByRank[iRank]);
    TheListOrbit:=[];
    for iOrbit in [1..nbOrbit]
    do
      ListNewStabGens:=[-IdentityMat(n)];
      for eGen in GeneratorsOfGroup(TheBound.ListOrbitByRank[iRank][iOrbit].TheStab)
      do
        Add(ListNewStabGens, RevTRS_SymmRep(n, eGen));
      od;
      TheNewStab:=Group(ListNewStabGens);
      #
      ListNewStabGensRot:=[-IdentityMat(n)];
      for eGen in GeneratorsOfGroup(TheBound.ListOrbitByRank[iRank][iOrbit].RotationSubgroup)
      do
        Add(ListNewStabGensRot, RevTRS_SymmRep(n, eGen));
      od;
      TheNewStabRot:=Group(ListNewStabGensRot);
      #
      TheNewListElt:=List(TheBound.ListOrbitByRank[iRank][iOrbit].BoundaryImage.ListElt, x->RevTRS_SymmRep(n,x));
      TheNewBound:=rec(ListIFace:=TheBound.ListOrbitByRank[iRank][iOrbit].BoundaryImage.ListIFace, 
                       ListSign:=TheBound.ListOrbitByRank[iRank][iOrbit].BoundaryImage.ListSign, ListElt:=TheNewListElt);
      NewSer:=rec(TheStab:=TheNewStab,
                  RotationSubgroup:=TheNewStabRot,
                  BoundaryImage:=TheNewBound);
      Add(TheListOrbit, NewSer);
    od;
    Add(TheNewListOrbitByRank, TheListOrbit);
  od;
  TheNewFuncSignatureDet:=function(iRank, iFace, eElt)
    return TheBound.FuncSignatureDet(iRank, iFace, TRS_SymmRep(eElt));
  end;
  TheNewIdentityElt:=IdentityMat(n);
  return rec(ListOrbitByRank:=TheNewListOrbitByRank, 
             FuncSignatureDet:=TheNewFuncSignatureDet,
             IdentityElt:=TheNewIdentityElt);
end;



GetEnumerationPerfectForm:=function(n)
  local TheTesselation, FuncInsert, IsFinished, nbRecord, SHVgroups, GramMat, GRP, ListPermGens, eGen, eList, PermGRP, ListSymm, ListOrbit, ListAdj, eOrb, FlippedGram, TheAdj, iRecord, GlobSymmGrp, eFac, TransformGroup, FuncDoRetraction, MyStab, OrbSize, iOrb, NewListPermGens, ePerm, eTransGen, FindPosition;
  TheTesselation:=[];
  GlobSymmGrp:=Group([-IdentityMat(n)]);
  TransformGroup:=function(TheGroup)
    local ListTransGens, eGen;
    ListTransGens:=List(GeneratorsOfGroup(TheGroup), TRS_SymmRep);
    return Group(ListTransGens);
  end;
  FuncInsert:=function(TheNewGram)
    local iRecord, eRecord, eEquiv, SHV, SHVgroups;
    for iRecord in [1..Length(TheTesselation)]
    do
      eRecord:=TheTesselation[iRecord];
      eEquiv:=ArithmeticEquivalenceMatrixFamily_Souvignier("", [eRecord.GramMat], [], [TheNewGram], []);
      if eEquiv<>false then
        return rec(iRecord:=iRecord, eEquiv:=TRS_SymmRep(Inverse(eEquiv)));
      fi;
    od;
    SHV:=ShortestVectorDutourVersion(TheNewGram);
    SHVgroups:=Orbits(GlobSymmGrp, SHV, OnPoints);
    eRecord:=rec(SHVgroups:=SHVgroups, GramMat:=TheNewGram, Status:="NO");
    Add(TheTesselation, eRecord);
    return rec(iRecord:=Length(TheTesselation), eEquiv:=TRS_SymmRep(IdentityMat(n)));
  end;
  FuncDoRetraction:=function(eVect)
    local nbDim, eMat;
    nbDim:=n*(n+1)/2;
    eMat:=VectorToSymmetricMatrix(eVect, n);
#    maybe this code is needed to get the correct
#    values of the fields.
#    for i in [1..n]
#    do
#      eMat[i][i]:=2*eMat[i][i];
#    od;
    if RankMat(eMat) < n then
      return true;
    else
      return false;
    fi;
  end;
  FuncInsert(LatticeAn(n).GramMat);
  while(true)
  do
    IsFinished:=true;
    nbRecord:=Length(TheTesselation);
    for iRecord in [1..nbRecord]
    do
      if TheTesselation[iRecord].Status="NO" then
        TheTesselation[iRecord].Status:="YES";
        IsFinished:=false;
        SHVgroups:=TheTesselation[iRecord].SHVgroups;
        GramMat:=TheTesselation[iRecord].GramMat;
        GRP:=ArithmeticAutomorphismMatrixFamily_Souvignier("", [GramMat], []);
        ListPermGens:=[];
        FindPosition:=function(eVect)
          local iGroup;
          for iGroup in [1..Length(SHVgroups)]
          do
            if Position(SHVgroups[iGroup], eVect)<>fail then
              return iGroup;
            fi;
          od;
        end;
        for eGen in GeneratorsOfGroup(GRP)
        do
          eList:=List(SHVgroups, x->FindPosition(x[1]*eGen));
          Add(ListPermGens, PermList(eList));
        od;
        PermGRP:=Group(ListPermGens);
        ListSymm:=List(SHVgroups, x->SymmetricMatrixToVector(TransposedMat([x[1]])*[x[1]]));
        ListOrbit:=DualDescriptionStandard(ListSymm, PermGRP);
        NewListPermGens:=[];
        for eGen in GeneratorsOfGroup(GRP)
        do
          eTransGen:=TRS_SymmRep(eGen);
          eList:=List(ListSymm, x->Position(ListSymm, x*eTransGen));
          ePerm:=PermList(eList);
          if ePerm=fail then
            Error("Please debug from here");
          fi;
          Add(NewListPermGens, ePerm);
        od;
        Print("|PermGRP|=", Order(PermGRP), "\n");
        for iOrb in [1..Length(ListOrbit)]
        do
          MyStab:=Stabilizer(PermGRP, ListOrbit[iOrb], OnSets);
          OrbSize:=Order(PermGRP)/Order(MyStab);
          Print(" iOrb=", iOrb, " |eOrb|=", Length(ListOrbit[iOrb]), " sizorb=", OrbSize, "\n");
        od;
        TheTesselation[iRecord].ListSymm:=ListSymm;
        TheTesselation[iRecord].PermGRP:=PermGRP;
        TheTesselation[iRecord].MatrixStab:=TransformGroup(GRP);
        ListAdj:=[];
        for eOrb in ListOrbit
        do
          FlippedGram:=DoFlipping_perfectform(SHVgroups, eOrb);
          TheAdj:=FuncInsert(FlippedGram);
          eFac:=FindFacetInequality(ListSymm, eOrb);
          TheAdj.eFac:=eFac;
          Add(ListAdj, TheAdj);
        od;
        TheTesselation[iRecord].ListAdj:=ListAdj;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  for iRecord in [1..Length(TheTesselation)]
  do
    Unbind(TheTesselation[iRecord].Status);
  od;
  return rec(TheTesselation:=TheTesselation, FuncDoRetraction:=FuncDoRetraction, TheGroup:=TransformGroup(GL(n, Integers)));
end;

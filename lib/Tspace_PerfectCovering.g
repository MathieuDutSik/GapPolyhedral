PERFCOV_GetRecordOfPerfectDomainIntersection:=function(eCase, TheGram)
  local n, BasisSpann, SHV, nbSHV, SHVred, ListRankOne, ListRankOneProj, FinRec, ListGramRay, CentGramMatrix, eEXT, eSymmMatProj, eGramRay, FAC, FACincd, eO, eRepr, eFAC, eIncd, RecDEBUG, GetConeInclusionTest;
  n:=Length(eCase.Basis[1]);
  BasisSpann:=List(eCase.Basis, SymmetricMatrixToVector);
  SHV:=ShortestVectorDutourVersion(TheGram);
  nbSHV:=Length(SHV)/2;
  SHVred:=List([1..nbSHV], x->SHV[2*x]);
  ListRankOne:=List(SHVred, x->TransposedMat([x]) * [x]);
  ListRankOneProj:=List(ListRankOne, SymmetricMatrixToVector);
  FinRec:=CONEINT_ComputeDoubleDescriptionIntersection(BasisSpann, ListRankOneProj);
#  RecDEBUG:=CONEINT_ComputeIntersectionDirectly(BasisSpann, ListRankOneProj);
  ListGramRay:=[];
  CentGramMatrix:=NullMat(n,n);
  for eEXT in FinRec.EXT
  do
    eSymmMatProj:=eEXT * BasisSpann;
    eGramRay:=RemoveFractionMatrix(VectorToSymmetricMatrix(eSymmMatProj, n));
    Add(ListGramRay, eGramRay);
    CentGramMatrix:=CentGramMatrix + eGramRay;
  od;
  GetConeInclusionTest:=function(EXT)
    local eFAC, eEXT, eScal;
    for eFAC in eCase.ListFacets
    do
      for eEXT in EXT
      do
        eScal:=eEXT*eFAC;
        if eScal<0 then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  FAC:=[];
  FACincd:=[];
  for eRepr in FinRec.LOrbFAC
  do
    eO:=Orbit(FinRec.GRPext, eRepr, OnSets);
    for eIncd in eO
    do
      eFAC:=__FindFacetInequality(FinRec.EXT, eIncd);
      Add(FAC, eFAC);
      Add(FACincd, eIncd);
    od;
  od;
  return rec(FinRec:=FinRec, EXT:=FinRec.EXT, FAC:=FAC, FACincd:=FACincd, IsInTheCone:=GetConeInclusionTest(FinRec.EXT), ListGramRay:=ListGramRay, SHV:=SHV, SHVred:=SHVred, CentGramMatrix:=CentGramMatrix, TheGram:=TheGram);
end;



IsGramMatrixIntersectingTransversally:=function(eCase, TheGram)
  local BasisSpann, SHV, nbSHV, SHVred, ListRankOne, ListRankOneProj, TheBasisInt, eDim;
  BasisSpann:=List(eCase.Basis, SymmetricMatrixToVector);
  SHV:=ShortestVectorDutourVersion(TheGram);
  nbSHV:=Length(SHV)/2;
  SHVred:=List([1..nbSHV], x->SHV[2*x]);
  ListRankOne:=List(SHVred, x->TransposedMat([x]) * [x]);
  ListRankOneProj:=List(ListRankOne, SymmetricMatrixToVector);
  TheBasisInt:=CONEINT_FindSpaceIntersection(BasisSpann, ListRankOneProj);
  eDim:=Length(eCase.Basis);
  if Length(TheBasisInt)=eDim then
    return true;
  fi;
  return false;
end;





FindPerfectContainingConfiguration:=function(SHV)
  local eRecTest, n, eCase, TheGram;
  eRecTest:=SHORT_TestRealizabilityShortestFamily(SHV);
  if eRecTest.reply=false then
    Error("We have just proven that there is no containing family");
  fi;
  n:=Length(SHV[1]);
  eCase:=GetStandardIntegralVoronoiSpace(n);
  TheGram:=GetOnePerfectFormKernel(eCase, eRecTest.eMat);
  return TheGram;
end;



# Given a positive definite form A, we want to find
# a perfect domain D that contains A.
GetContainingPerfectDomain:=function(GramMat)
  local GramMatVect, eG, eSHV, TheGram, SHV, nbSHV, SHVred, n, ListRankOne, ListRankOneVect, ListVect, TheRel, TheSubset, SHVgroups;
  GramMatVect:=SymmetricMatrixToVector(GramMat);
  eG:=Inverse(GramMat);
  eSHV:=ShortestVectorDutourVersion(eG);
  nbSHV:=Length(eSHV)/2;
  SHVred:=List([1..nbSHV], x->eSHV[2*x-1]);
  #
  n:=Length(GramMat);
  if RankMat(SHVred)=n then
    # This is an ansatz actually to have a better guess
    TheGram:=FindPerfectContainingConfiguration(SHVred);
  else
    TheGram:=LatticeAn(n).GramMat;
  fi;
  while(true)
  do
    SHV:=ShortestVectorDutourVersion(TheGram);
    nbSHV:=Length(SHV)/2;
    SHVred:=List([1..nbSHV], x->SHV[2*x-1]);
    ListRankOne:=List(SHVred, x->TransposedMat([x])*[x]);
    ListRankOneVect:=List(ListRankOne, SymmetricMatrixToVector);
    ListVect:=Concatenation(ListRankOneVect, [-GramMatVect]);
    TheRel:=SearchPositiveRelationSimple(ListVect);
    if TheRel<>false then
      return rec(TheGram:=TheGram, SHV:=SHV, SHVred:=SHVred, ListRankOne:=ListRankOne, ListRankOneVect:=ListRankOneVect);
    fi;
    SHVgroups:=List(SHVred, x->[x, -x]);
    TheSubset:=GetViolatedFacet(ListRankOneVect, GramMatVect);
    TheGram:=DoFlipping_perfectform(SHVgroups, TheSubset);
  od;
end;




MossContraction:=function(GramMat)
  local n, GramMatVect, eRec, ListRankOneVect, eRecSimplex, ListForm, eSet, eForm, i, eVect, ListFormVect, ListRank, len, eSol, eFormRet, eVal;
  n:=Length(GramMat);
  GramMatVect:=SymmetricMatrixToVector(GramMat);
  eRec:=GetContainingPerfectDomain(GramMat);
  ListRankOneVect:=eRec.ListRankOneVect;
  eRecSimplex:=GetContainingSimplex(ListRankOneVect, GramMatVect);
  ListForm:=[];
  for eSet in eRecSimplex.ListSet
  do
    eForm:=NullMat(n,n);
    for i in eSet
    do
      eVect:=eRec.SHVred[i];
      eForm:=eForm + TransposedMat([eVect])*[eVect];
    od;
    Add(ListForm, eForm);
  od;
  ListFormVect:=List(ListForm, SymmetricMatrixToVector);
  ListRank:=List(ListForm, RankMat);
  len:=Length(ListRank);
  eSol:=SolutionMat(ListFormVect, GramMatVect);
  eFormRet:=NullMat(n,n);
  for i in [1..len]
  do
    eVal:=eSol[i];
    if eVal<0 then
      Error("We are not in the simplex. Bug to solve");
    fi;
    if ListRank[i]=n then
      eFormRet:=eFormRet + eSol[i]*ListForm[i];
    fi;
  od;
  return eFormRet;
end;




PERFCOV_FuncPrintTiling:=function(output, ListInfo)
  local iTile, iOrbit, eRec, eSHVred;
  iTile:=0;
  iOrbit:=0;
  for eRec in ListInfo
  do
    iOrbit:=iOrbit+1;
    for eSHVred in eRec.ListSHVred
    do
      iTile:=iTile+1;
      AppendTo(output, "Tile Nr=", iTile, " Orbit Nr=", iOrbit, " InCone=", eRec.IsInTheCone, " InSubspace=", eRec.IsFullContSubspace, "\n");
      WriteMatrix(output, eSHVred);
    od;
  od;
end;




# eCase is the same as in the function Kernel_GetEnumerationPerfectForm
# 
#
PERFCOV_GetPerfectCoveringDomains:=function(eCase)
  local n, DimSpace, RecExtRay, TheTesselation, FuncInsert, nbTotalPerfect, IsFinished, i, TheGram, TheRec, GetOrbitsFacets, TryInsert, BasisProj, SuperProj, SuperExpr, DoFlipping, eFlip, eVectRand, result, LOrb, eOrb, IsInTheCone;
  n:=Length(eCase.Basis[1]);
  DimSpace:=Length(eCase.Basis);
  RecExtRay:=TSPACE_GetExtremeRayFunctions(eCase);
  TheTesselation:=[];
  nbTotalPerfect:=0;
  BasicCoherencyCheckups(eCase);
  #
  # The gram matrix put here must define a correct domain
  #
  FuncInsert:=function(RecInfo)
    local SHVdisc, SHV, eInv, extRaySig, iRecord, eRecord, test, NewRecord, eStab, TheRec, OrbSize;
    SHVdisc:=__ExtractInvariantZBasisShortVectorNoGroup(RecInfo.CentGramMatrix);
    # We need to compute the polyhedral intersection
    eInv:=KernelGetInvariantGram(RecInfo.CentGramMatrix, SHVdisc);
    extRaySig:=RecExtRay.GetExtRaySignature(RecInfo.CentGramMatrix);
    eInv.CollExt:=Collected(extRaySig);
    for iRecord in [1..Length(TheTesselation)]
    do
      eRecord:=TheTesselation[iRecord];
      if eRecord.eInv=eInv then
        test:=RepresentativeAction(RecExtRay.PermGrpExtRays, extRaySig, eRecord.extRaySig, Permuted);
        if test<>fail then
          return;
        fi;
      fi;
    od;
    eStab:=Stabilizer(RecExtRay.PermGrpExtRays, extRaySig, Permuted);
    OrbSize:=Order(RecExtRay.PermGrpExtRays)/Order(eStab);
    nbTotalPerfect:=nbTotalPerfect + OrbSize;
    NewRecord:=rec(eInv:=eInv, OrbSize:=OrbSize, extRaySig:=extRaySig, RecInfo:=RecInfo, Status:="NO");
    Add(TheTesselation, NewRecord);
    Print("Now |TheTesselation|=", Length(TheTesselation), "\n");
  end;
  GetOrbitsFacets:=function(eRecord)
    local eStab, ListCharVect, eEXT, eCharVect, ListPermGens, eGen, eList, GRPext, O, LOrb, eO, eIncd, pos, eFAC, eOrb, eGramRay;
    eStab:=Stabilizer(RecExtRay.PermGrpExtRays, eRecord.extRaySig, Permuted);
    ListCharVect:=[];
    for eGramRay in eRecord.RecInfo.ListGramRay
    do
      eCharVect:=RecExtRay.GetExtRaySignature(eGramRay);
      Add(ListCharVect, eCharVect);
    od;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(eStab)
    do
      eList:=List(ListCharVect, x->Position(ListCharVect, Permuted(x, eGen)));
      Add(ListPermGens, PermList(eList));
    od;
    GRPext:=PersoGroupPerm(ListPermGens);
    O:=Orbits(GRPext, eRecord.RecInfo.FACincd, OnSets);
    LOrb:=[];
    for eO in O
    do
      eIncd:=eO[1];
      pos:=Position(eRecord.RecInfo.FACincd, eIncd);
      eFAC:=eRecord.RecInfo.FAC[pos];
      eOrb:=rec(eFAC:=eFAC, eIncd:=eIncd);
      Add(LOrb, eOrb);
    od;
    return LOrb;
  end;
  DoFlipping:=function(eRecInfo, eOrb)
    local TheRayFacet, TheGramFacet, iEXT, eDiff, eScal, eGramCand, eGramPerfect, NewRecInfo, eSol, testIntersection;
    TheRayFacet:=ListWithIdenticalEntries(DimSpace, 0);
    TheGramFacet:=NullMat(n,n);
    for iEXT in eOrb.eIncd
    do
      TheRayFacet:=TheRayFacet + eRecInfo.EXT[iEXT];
      TheGramFacet:=TheGramFacet + eRecInfo.ListGramRay[iEXT];
    od;
    if RankMat(TheGramFacet)<n then
      return fail;
    fi;
    eDiff:=TheGramFacet - eRecInfo.CentGramMatrix;
    eScal:=1;
    while(true)
    do
      eGramCand:=TheGramFacet + eScal * eDiff;
      if IsPositiveDefiniteSymmetricMatrix(eGramCand) then
        eGramPerfect:=GetContainingPerfectDomain(eGramCand).TheGram;
	Print("eGramPerfect=", eGramPerfect, "\n");
        if IsGramMatrixIntersectingTransversally(eCase, eGramPerfect) then
          NewRecInfo:=PERFCOV_GetRecordOfPerfectDomainIntersection(eCase, eGramPerfect);
          eSol:=SolutionMatNonnegative(NewRecInfo.EXT, TheRayFacet);
          Print("eSol=", eSol, "\n");
          if eSol<>fail then
            testIntersection:=POLYDEC_HasConeNonVoidIntersection(eCase, NewRecInfo.FAC);
            if testIntersection then
              return NewRecInfo;
            else
              return fail;
            fi;
          fi;
        fi;
      fi;
      Print("eScal=", eScal, "\n");
      eScal:=eScal / 2;
    od;
  end;
  BasisProj:=List(eCase.Basis, SymmetricMatrixToVector);
  SuperProj:=SymmetricMatrixToVector(eCase.SuperMat);
  SuperExpr:=SolutionMat(BasisProj, SuperProj);
  TryInsert:=function(eVect)
    local eCoeff, eVectAtp, eFirst, eGram, i, eGramPerfect, eRecInfo;
    eCoeff:=1;
    while(true)
    do
      eVectAtp:=eVect + eCoeff * SuperExpr;
      eFirst:=First(eCase.ListFacets, x->x*eVectAtp<=0);
      if eFirst=fail then
        break;
      fi;
      eCoeff:=eCoeff+1;
    od;
    eGram:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      eGram:=eGram + eVectAtp[i] * eCase.Basis[i];
    od;
    eGramPerfect:=GetContainingPerfectDomain(eGram).TheGram;
    if IsGramMatrixIntersectingTransversally(eCase, eGramPerfect) then
      eRecInfo:=PERFCOV_GetRecordOfPerfectDomainIntersection(eCase, eGramPerfect);
      FuncInsert(eRecInfo);
      return true;
    fi;
    return false;
  end;
  while(true)
  do
    eVectRand:=[];
    for i in [1..DimSpace]
    do
      Add(eVectRand, Random([-2..2]));
    od;
    result:=TryInsert(eVectRand);
    if result then
      break;
    fi;
  od;
  while(true)
  do
    IsFinished:=true;
    for i in [1..Length(TheTesselation)]
    do
      if TheTesselation[i].Status="NO" then
        Print("Treating Orbit i=", i, "\n");
        TheTesselation[i].Status:="YES";
        IsFinished:=false;
        LOrb:=GetOrbitsFacets(TheTesselation[i]);
        for eOrb in LOrb
        do
          eFlip:=DoFlipping(TheTesselation[i].RecInfo, eOrb);
          if eFlip<>fail then
            FuncInsert(eFlip);
          fi;
        od;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  Print("|TheTesselation|=", Length(TheTesselation), " nbTotalPerfect=", nbTotalPerfect, "\n");
  return rec(TheTesselation:=TheTesselation,
             nbTotalPerfect:=nbTotalPerfect);
end;



PERFCOV_FuncGetCollectionTiling:=function(eCase, TheTesselation)
  local BasisProj, ListInfo, TheAct, TheActConj, eRec, SHVred, ListRankOne, ListRankOneProj, CentProj, eIncd, SHV, eO, ListSHVred, ListRecord, IsFullContSubspace, IsFullyContainedSubspace;
  BasisProj:=List(eCase.Basis, SymmetricMatrixToVector);
  ListInfo:=[];
  TheAct:=function(x, g)
    return Set(List(x, u->u*CongrMap(g)));
  end;
  TheActConj:=function(x, g)
    return g * x * TransposedMat(g);
  end;
  IsFullyContainedSubspace:=function(ListExtRay)
    local eRay;
    for eRay in ListExtRay
    do
      if SolutionMat(BasisProj, eRay)=fail then
        return false;
      fi;
    od;
    return true;
  end;
  for eRec in TheTesselation
  do
    SHVred:=eRec.RecInfo.SHVred;
    ListRankOne:=List(SHVred, x->TransposedMat([x]) * [x]);
    ListRankOneProj:=List(ListRankOne, SymmetricMatrixToVector);
    CentProj:=SymmetricMatrixToVector(eRec.RecInfo.CentGramMatrix);
    eIncd:=GetContainingFacet(ListRankOneProj, CentProj);
    SHV:=Set(Concatenation(SHVred{eIncd}, -SHVred{eIncd}));
    eO:=Orbit(eCase.SymmGrpGlob, SHV, TheAct);
    if Length(eO)<>eRec.OrbSize then
      Error("We have an orbit inconsistency");
    fi;
    ListSHVred:=List(eO, SHORT_CleanAntipodality);
    IsFullContSubspace:=IsFullyContainedSubspace(ListRankOneProj{eIncd});
    Add(ListInfo, rec(OrbSize:=Length(ListSHVred), IsInTheCone:=eRec.RecInfo.IsInTheCone, IsFullContSubspace:=IsFullContSubspace, ListSHVred:=ListSHVred));
  od;
  return ListInfo;
end;

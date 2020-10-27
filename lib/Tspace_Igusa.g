# The Igusa theory of central cones generalized to
# the Tspace setting.
#
IGUSA_IntegralMinimizationOverTspace:=function(eCase, ListGramInt, LinearFunc)
  local n, DimSpace, GetIneq, ListIneqTotal, eGram, SHV, ListIneq, UpdateListIneqFromMatSol, LinearFuncExt, TheLP, eVectEmb, eMatSol, eEnt, eSol, IsCorrect, i, BasisExpand, eGramExp, eVectGram, ListScal, ListVectTotal, DoReductionIneq, iter, TheGramContain, SHVcontain, eRecContain, GetIneqRed, eGramExpand, ListGramInt_Expr, ListVal, eValPlane, TheRel, ListVectIneq, TheSum, TheLP_glpk;
  DimSpace:=Length(eCase.Basis);
  n:=Length(eCase.Basis[1]);
  GetIneq:=function(eSHV)
    return Concatenation([-1], List(eCase.Basis, x->eSHV*x*eSHV));
  end;
  GetIneqRed:=function(eSHV)
    return List(eCase.Basis, x->eSHV*x*eSHV);
  end;
  ListIneqTotal:=[];
  ListVectTotal:=[];
  DoReductionIneq:=function()
    local ListPos;
    ListPos:=List(Set(ListIneqTotal), x->Position(ListIneqTotal, x));
    ListIneqTotal:=ListIneqTotal{ListPos};
    ListVectTotal:=ListVectTotal{ListPos};
  end;
  BasisExpand:=List(eCase.Basis, SymmetricMatrixToVector);
  ListGramInt_Expr:=[];
  for eGram in ListGramInt
  do
    if IsPositiveDefiniteSymmetricMatrix(eGram)=false then
      Error("All matrices need to be positive definite");
    fi;
    if IsQuadFormIntegralValued(eGram)=false then
      Error("All matrices should be integral valued");
    fi;
    SHV:=ShortestVectorDutourVersion(eGram);
    Append(ListVectTotal, SHV);
    Append(ListIneqTotal, List(SHV, GetIneq));
    eGramExpand:=SymmetricMatrixToVector(eGram);
    Add(ListGramInt_Expr, SolutionMat(BasisExpand, eGramExpand));
  od;
  ListVal:=List(ListGramInt_Expr, x->x*LinearFunc);
  if Length(Set(ListVal))<>1 then
    Error("Not all integral input matrices are on the function plane");
  fi;
  eValPlane:=ListVal[1];
  DoReductionIneq();
  eRecContain:=TSPACE_GetContainingPerfectDomain(eCase, LinearFunc);
  SHVcontain:=ShortestVectorDutourVersion(eRecContain.TheGram);
  Append(ListVectTotal, SHVcontain);
  Append(ListIneqTotal, List(SHVcontain, GetIneq));
  for eGram in ListGramInt
  do
    eGramExp:=SymmetricMatrixToVector(eGram);
    eVectGram:=Concatenation([1], SolutionMat(BasisExpand, eGramExp));
    ListScal:=List(ListIneqTotal, x->x*eVectGram);
    if Minimum(ListScal) < 0 then
      Error("Error in minimum");
    fi;
  od;
  UpdateListIneqFromMatSol:=function(eMatSol)
    local NSP, ListIneq, eRecShort, iShort, nbShort, SHV, NewVect;
    if RankMat(eMatSol) < n then
      NSP:=NullspaceIntMat(RemoveFractionMatrix(eMatSol));
      Print("NSP=", NSP, "\n");
      ListIneq:=List(NSP, GetIneq);
      Append(ListVectTotal, NSP);
      Append(ListIneqTotal, ListIneq);
      IsCorrect:=false;
      Print("Case 1\n");
    else
      if IsPositiveDefiniteSymmetricMatrix(eMatSol) then
        eRecShort:=ShortestVectors(eMatSol, 1);
        nbShort:=Length(eRecShort.norms);
        IsCorrect:=true;
        SHV:=[];
        for iShort in [1..nbShort]
        do
          if eRecShort.norms[iShort] < 1 then
            Add(SHV, eRecShort.vectors[iShort]);
            IsCorrect:=false;
          fi;
        od;
        ListIneq:=List(SHV, GetIneq);
        Append(ListVectTotal, SHV);
        Append(ListIneqTotal, ListIneq);
        Print("Case 2\n");
      else
        IsCorrect:=false;
        NewVect:=EigenvalueFindNegativeVect(eMatSol);
        Print("NewVect=", NewVect, "\n");
        Add(ListVectTotal, NewVect);
        Add(ListIneqTotal, GetIneq(NewVect));
        Print("Case 3\n");
      fi;
    fi;
  end;
  LinearFuncExt:=Concatenation([-eValPlane], LinearFunc);
  iter:=0;
  while(true)
  do
    DoReductionIneq();
    iter:=iter+1;
    Print("LP: iter=", iter, " |ListVectTotal|=", Length(ListVectTotal), "\n");
    TheLP:=LinearProgramming(ListIneqTotal, LinearFuncExt);
    Print("After LP\n");
    if IsBound(TheLP.optimal)=false then
      Error("More programming is needed");
    fi;
    if TheLP.optimal=0 then
      TheSum:=ListWithIdenticalEntries(Length(LinearFuncExt),0);
      TheSum:=TheSum + LinearFuncExt;
      for eEnt in TheLP.dual_solution
      do
        if eEnt[2]>0 then
          Error("Problem in our understanding. It happens");
        fi;
        TheSum:=TheSum + eEnt[2]*ListIneqTotal[eEnt[1]];
      od;
      if TheSum<>ListWithIdenticalEntries(Length(LinearFuncExt),0) then
        Error("Again a conceptual problem");
      fi;
      return rec(eMatSol:=ListGramInt[1]);
    fi;
    Print("opti=", TheLP.optimal, "\n");
    eVectEmb:=ListWithIdenticalEntries(Length(eCase.Basis),0);
    eMatSol:=NullMat(n,n);
    for eEnt in TheLP.primal_solution
    do
      eVectEmb[eEnt[1]]:=eEnt[2];
      eMatSol:=eMatSol + eEnt[2]*eCase.Basis[eEnt[1]];
    od;
    UpdateListIneqFromMatSol(eMatSol);
    if IsCorrect=true then
      break;
    fi;
  od;
  if IsQuadFormIntegralValued(eMatSol) then
    Print("Finish with integral matrix by the LP\n");
    return rec(eMatSol:=eMatSol);
  fi;
  # Now doing the integral optimization !
  iter:=0;
  while(true)
  do
    Print("|ListIneqTotal|=", Length(ListIneqTotal), "\n");
    Print("ILP: iter=", iter, " |ListVectTotal|=", Length(ListVectTotal), "\n");
    TheLP_glpk:=GLPK_IntegerLinearProgramming(ListIneqTotal, LinearFuncExt);
    eSol:=TheLP_glpk.eVect;
    eMatSol:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      eMatSol:=eMatSol + eSol[i]*eCase.Basis[i];
    od;
    UpdateListIneqFromMatSol(eMatSol);
    if IsCorrect=true then
      break;
    fi;
  od;
  return rec(eMatSol:=eMatSol);
end;

DUAL_InquireRec:=function(ePrefix, EXT, GRP)
  local iFile, eFile, RecRead, eEquiv, GRPconj, NewListOrb, ListIneq;
  iFile:=1;
  while(true)
  do
    eFile:=Concatenation(ePrefix, String(iFile));
    if IsExistingFilePlusTouch(eFile)=false then
      return fail;
    fi;
    Print("Reading from eFile=", eFile, "\n");
    RecRead:=ReadAsFunction(eFile)();
    Print("|RecRead.EXT|=", Length(RecRead.EXT), " |RecRead.GRP|=", Order(RecRead.GRP), "\n");
    if RecRead.EXT=EXT and RecRead.GRP=GRP then
      return RecRead.ListOrb;
    fi;
    if Length(EXT)>10000 then
      eEquiv:=LinPolytope_IsomorphismHeuristic(RecRead.EXT, EXT);
      if eEquiv<>false then
        Print("eEquiv <> false\n");
        GRPconj:=Group(List(GeneratorsOfGroup(RecRead.GRP), x->Inverse(eEquiv)*x*eEquiv));
        if GRPconj=GRP then
          Print("GRPconj = GRP\n");
          NewListOrb:=List(RecRead.ListOrb, x->OnSets(x, eEquiv));
          ListIneq:=List(NewListOrb, x->__FindFacetInequality(EXT, x));
          return NewListOrb;
        fi;
      fi;
    fi;
    iFile:=iFile+1;
  od;
end;

DUAL_ReturnEmptyFile:=function(ePrefix)
  local iFile, eFile;
  iFile:=1;
  while(true)
  do
    eFile:=Concatenation(ePrefix, String(iFile));
    if IsExistingFilePlusTouch(eFile)=false then
      return eFile;
    fi;
    iFile:=iFile+1;
  od;
end;


IGUSA_FindListNeighboringIntegralMat:=function(eCase, TheGram, Data, BF)
  local ListAdj, ListAdjInt, SHVdisc, TheFormalDisc, SingleOrbInfo, TheGramExpr, TheAct, ComputeGroupListDirAdj, ListOrb, IsFinished, eOrb, eFAC, eRecSol, eMatSolExpr, eScal, Onew, O, ListOrbitAdjacent, ListDirAdj, GRPadjInt, ListGram, DirSel, eSet, BasisExpand, eMatSolBas, UpdateByFacetInequality, RedIsomorphy, nbIterNoUpdate, ListSet, nb, nbOrb, iOrb, i, j, DimSpa, MatScalar, ListRayMat, ListMatEqua, n, ListSol, ListEqua, eDiff, iMat, eNSP, NSP, eRayMat, eRepr, eMat, fRayMat, gRayMat, eRecIAI, TheLimit, FuncStabilizer, FuncIsomorphy, FuncInvariant, BFloc, BankPath, Saving, GroupFormalism, ePrefix, eInq, eFile, eRecTriple;
  ListAdj:=FindAllRyshkovNeighbors(eCase, TheGram);
  ListAdjInt:=Filtered(ListAdj, IsQuadFormIntegralValued);
  SHVdisc:=__ExtractInvariantZBasisShortVectorNoGroup(TheGram);
  TheFormalDisc:=TspaceFormalism(eCase, SHVdisc);
  BasisExpand:=List(eCase.Basis, SymmetricMatrixToVector);
  DimSpa:=Length(eCase.Basis);
  MatScalar:=NullMat(DimSpa, DimSpa);
  n:=Length(eCase.Basis[1]);
  for i in [1..DimSpa]
  do
    for j in [1..DimSpa]
    do
      eScal:=Trace(eCase.Basis[i]*eCase.Basis[j]);
      MatScalar[i][j]:=eScal;
    od;
  od;
  SingleOrbInfo:=GetStabilizerTspace(eCase, TheFormalDisc, TheGram);
  TheGramExpr:=SymmetricMatrixToVector(TheGram);
  TheAct:=function(x, g)
    return g*x*TransposedMat(g);
  end;
  ComputeGroupListDirAdj:=function()
    local ListPermGens, eGen, eList, eAdjInt, eAdjIntExpr, eDirInt;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(SingleOrbInfo.TheStabMatr)
    do
      eList:=List(ListAdjInt, x->Position(ListAdjInt, eGen*x*TransposedMat(eGen)));
      Add(ListPermGens, PermList(eList));
    od;
    GRPadjInt:=Group(ListPermGens);
    ListDirAdj:=[];
    for eAdjInt in ListAdjInt
    do
      eAdjIntExpr:=SymmetricMatrixToVector(eAdjInt);
      eDirInt:=RemoveFraction(SolutionMat(BasisExpand, eAdjIntExpr - TheGramExpr));
      Add(ListDirAdj, eDirInt);
    od;
    Print("|ListDirAdj|=", Length(ListDirAdj), " rnk(ListDirAdj)=", RankMat(ListDirAdj), "\n");
    Print("|GRPadj|=", Order(GRPadjInt), "\n");
  end;
  RedIsomorphy:=function()
    local BoundingSet, eRec, ListAdjInt;
    BoundingSet:=[];
    eRec:=EliminationByRedundancyEquivariant(ListDirAdj, BoundingSet, GRPadjInt);
    Print("|eSetSelect|=", Length(eRec.eSetSelect), "\n");
    if Length(eRec.eSetSelect)=Length(ListDirAdj) then
      return;
    fi;
    ListAdjInt:=ListAdjInt{eRec.eSetSelect};
    ComputeGroupListDirAdj();
  end;
  #
  UpdateByFacetInequality:=function(eOrbIns)
    local eFAC, ListGram, eRecSol, eMatSolExpr, eMatSolBas, eScal, Onew;
    eFAC:=__FindFacetInequality(ListDirAdj, eOrbIns);
    ListGram:=Concatenation([TheGram], ListAdjInt{eOrbIns});
    eRecSol:=IGUSA_IntegralMinimizationOverTspace(eCase, ListGram, eFAC);
    eMatSolExpr:=SymmetricMatrixToVector(eRecSol.eMatSol);
    eMatSolBas:=SolutionMat(BasisExpand, eMatSolExpr - TheGramExpr);
    eScal:=eFAC*eMatSolBas;
    if eScal<0 then
      Onew:=Orbit(SingleOrbInfo.TheStabMatr, eRecSol.eMatrSol, TheAct);
      Append(ListAdjInt, Onew);
      IsFinished:=false;
    fi;
  end;
  #
  # Starting random updates procedure
  #
  nbIterNoUpdate:=0;
  while(true)
  do
    if nbIterNoUpdate=0 then
      break;
    fi;
    ComputeGroupListDirAdj();
    nbIterNoUpdate:=nbIterNoUpdate+1;
    IsFinished:=true;
    nb:=10;
    ListSet:=GetInitialRays_LinProg(ListDirAdj, nb);
    for eSet in ListSet
    do
      UpdateByFacetInequality(eSet);
    od;
    ComputeGroupListDirAdj();
    RedIsomorphy();
    Print("nbIterNoUpdate = ", nbIterNoUpdate, "\n");
    if IsFinished=false then
      nbIterNoUpdate:=0;
    fi;
  od;
  #
  # Now iterating with dual descriptions.
  #
  Print("Beginning the MEGA LOOP\n");
  while(true)
  do
    ComputeGroupListDirAdj();
    Print("After ComputeGroupListDirAdj\n");
    BankPath:="/irrelevant/";
    Saving:=false;
    TheLimit:=250;
    Print("Before GetIAI...\n");
    eRecIAI:=GetIAI_FromEXT_GRP(ListDirAdj, GRPadjInt, TheLimit);
    Print("After eRecIAI\n");
    FuncStabilizer:=eRecIAI.FuncStabilizer;
    FuncIsomorphy:=eRecIAI.FuncIsomorphy;
    FuncInvariant:=eRecIAI.FuncInvariant;
    GroupFormalism:=OnSetsGroupFormalism(500);
    Print("Before call for BFloc\n");
    ePrefix:="TripleEXT_GRP_LOrb";
    eInq:=DUAL_InquireRec(ePrefix, ListDirAdj, GRPadjInt);
    if eInq=fail then
      if Length(ListDirAdj) > 10000 then
        Error("Debug from that point");
      fi;
      BFloc:=BankRecording(rec(Saving:=Saving, BankPath:=BankPath), FuncStabilizer, FuncIsomorphy, FuncInvariant, GroupFormalism);
      Print("Before call for ListOrb\n");
      SaveDataToFile("PairInstability", rec(EXT:=ListDirAdj, GRP:=GRPadjInt));
      ListOrb:=__ListFacetByAdjacencyDecompositionMethod(ListDirAdj, GRPadjInt, Data, BFloc);
      BFloc.FuncClearAccount();
      eFile:=DUAL_ReturnEmptyFile(ePrefix);
      eRecTriple:=rec(EXT:=ListDirAdj, GRP:=GRPadjInt, ListOrb:=ListOrb);
      SaveDataToFilePlusTouch(eFile, eRecTriple);
    else
      ListOrb:=eInq;
    fi;
    #
    IsFinished:=true;
    nbOrb:=Length(ListOrb);
    for iOrb in [1..nbOrb]
    do
      Print("iOrb=", iOrb, "/", nbOrb, "\n");
      eOrb:=ListOrb[iOrb];
      UpdateByFacetInequality(eOrb);
    od;
    if IsFinished=true then
      break;
    fi;
    ComputeGroupListDirAdj();
    RedIsomorphy();
  od;
  Print("|ListDirAdj|=", Length(ListDirAdj), "\n");
  O:=Orbits(SingleOrbInfo.TheStabMatr, ListAdjInt, TheAct);
  ListOrbitAdjacent:=List(O, x->x[1]);
  ListRayMat:=[];
  for eOrb in ListOrb
  do
    for eRepr in Orbit(GRPadjInt, eOrb, OnSets)
    do
      ListMatEqua:=Concatenation([TheGram], ListAdjInt{eRepr});
      ListSol:=[];
      for eMat in ListMatEqua
      do
        Add(ListSol, SolutionMat(BasisExpand, SymmetricMatrixToVector(eMat)));
      od;
      ListEqua:=[];
      for iMat in [2..Length(ListMatEqua)]
      do
        eDiff:=ListSol[iMat] - ListSol[1];
        Add(ListEqua, eDiff*MatScalar);
      od;
      NSP:=NullspaceMat(TransposedMat(ListEqua));
      if Length(NSP)<>1 then
        Error("Error in size of NSP");
      fi;
      eNSP:=NSP[1];
      eRayMat:=NullMat(n, n);
      for i in [1..DimSpa]
      do
        eRayMat:=eRayMat + eCase.Basis[i]*eNSP[i];
      od;
      fRayMat:=RemoveFractionMatrix(eRayMat);
      if Trace(fRayMat)<0 then
        gRayMat:=-fRayMat;
      else
        gRayMat:=fRayMat;
      fi;
      Add(ListRayMat, gRayMat);
    od;
  od;
  return rec(ListOrbitAdjacent:=ListOrbitAdjacent, ListAdjInt:=ListAdjInt, ListOrb:=ListOrb, ListRayMat:=ListRayMat);
end;

IGUSA_GetVerticesPolyhedron:=function(eCaseGen2)
  local n, TheTesselation, TheBasis, DimSpace, TheBasisExpand, FuncInsert, IsFinished, nbRecord, iRecord, ListOrbAdjInt, eAdjInt, TheAdj, GramMat, ListAdj, eRecAdj, BankPath, Saving, SavingIrrelevant, IsRespawn, IsBankSave, TheFunc, Data, FuncStabilizer, FuncIsomorphy, FuncInvariant, GroupFormalism, BF, TmpDir, PathSave;
  n:=Length(eCaseGen2.SuperMat[1]);
  TheTesselation:=[];
  if IsTspaceBasisIntegral(eCaseGen2.Basis)=false then
    Error("The basis is not integral");
  fi;
  if IsBound(eCaseGen2.BankPath) then
    BankPath:=eCaseGen2.BankPath;
    Exec("mkdir -p ", BankPath);
    Saving:=true;
  else
    BankPath:="/irrelevant/";
    Saving:=false;
  fi;
  FuncStabilizer:=LinPolytope_Automorphism;
  FuncIsomorphy:=LinPolytope_Isomorphism;
  FuncInvariant:=LinPolytope_Invariant;
  GroupFormalism:=OnSetsGroupFormalism(500);
  BF:=BankRecording(rec(Saving:=Saving, BankPath:=BankPath), FuncStabilizer, FuncIsomorphy, FuncInvariant, GroupFormalism);
  if IsBound(eCaseGen2.IsRespawn) then
    IsRespawn:=eCaseGen2.IsRespawn;
  else
    IsRespawn:=function(OrdGRP, EXT, TheDepth)
      local nbInc;
      nbInc:=Length(EXT);
      if nbInc <= 50 then
        return false;
      fi;
      if nbInc>90 and OrdGRP>50 then
        return true;
      fi;
      if TheDepth>=2 then
        return false;
      fi;
      if OrdGRP>=200 then
        return true;
      fi;
      return true;
    end;
  fi;
  if IsBound(eCaseGen2.IsBankSave) then
    IsBankSave:=eCaseGen2.IsBankSave;
  else
    IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
      if TheDepth=0 then
        return false;
      fi;
      if EllapsedTime>=600 then
        return true;
      fi;
      if Length(EXT)<=27 then
        return false;
      fi;
      return true;
    end;
  fi;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  PathSave:="/irrelevant/";
  SavingIrrelevant:=false;
  TheFunc:=function(EXT, GRP, ThePath)
    return __DualDescriptionCDD_Reduction(EXT, GRP, ThePath);
  end;
  Data:=rec(TheDepth:=0,
            ThePath:=TmpDir,
            GetInitialRays:=GetInitialRays_LinProg, 
            IsBankSave:=IsBankSave,
            GroupFormalism:=OnSetsGroupFormalism(500), 
            DualDescriptionFunction:=TheFunc, 
            IsRespawn:=IsRespawn,
            Saving:=SavingIrrelevant,
            ThePathSave:=PathSave);
  TheBasis:=eCaseGen2.Basis;
  DimSpace:=Length(TheBasis);
  TheBasisExpand:=List(TheBasis, SymmetricMatrixToVector);
  FuncInsert:=function(TheNewGram)
    local iRecord, eRecord, eEquiv, SHV, SHVdisc, SHVrecord, eEquivInfo, eSol, GramMatExpand, eInv;
    SHVdisc:=__ExtractInvariantZBasisShortVectorNoGroup(TheNewGram);
    eInv:=KernelGetInvariantGram(TheNewGram, SHVdisc);
    for iRecord in [1..Length(TheTesselation)]
    do
      eRecord:=TheTesselation[iRecord];
      if eRecord.eInv=eInv then
        SHVrecord:=TheTesselation[iRecord].SHVdisc;
        eEquivInfo:=TestEquivalenceTspace(eCaseGen2, SHVrecord, eRecord.GramMat, SHVdisc, TheNewGram);
        if eEquivInfo<>fail then
          return rec(iRecord:=iRecord, 
                     eEquivDirect:=eEquivInfo.eEquivTspace, 
                     eEquiv:=eEquivInfo.eEquivTspaceTrI);
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
    Add(TheTesselation, eRecord);
    Print("Now we have ", Length(TheTesselation), " Igusa forms\n");
    return rec(iRecord:=Length(TheTesselation), 
               eEquivDirect:=IdentityMat(DimSpace), 
               eEquiv:=IdentityMat(DimSpace));
  end;
  # A hack at the present time. Enough for the time being.
  # The supermat does not have to be a vertex of the Igusa complex.
  FuncInsert(eCaseGen2.SuperMat);
  while(true)
  do
    IsFinished:=true;
    nbRecord:=Length(TheTesselation);
    for iRecord in [1..nbRecord]
    do
      if TheTesselation[iRecord].Status="NO" then
        TheTesselation[iRecord].Status:="YES";
        IsFinished:=false;
        GramMat:=TheTesselation[iRecord].GramMat;
        eRecAdj:=IGUSA_FindListNeighboringIntegralMat(eCaseGen2, GramMat, Data, BF);
        ListAdj:=[];
        for eAdjInt in eRecAdj.ListOrbitAdjacent
        do
          TheAdj:=FuncInsert(eAdjInt);
          TheAdj.FlippedGram:=eAdjInt;
          Add(ListAdj, TheAdj);
        od;
        TheTesselation[iRecord].ListAdj:=ListAdj;
        TheTesselation[iRecord].eRecAdj:=eRecAdj;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  Print("We find ", Length(TheTesselation), " Igusa forms\n");
  return rec(TheTesselation:=TheTesselation);
end;



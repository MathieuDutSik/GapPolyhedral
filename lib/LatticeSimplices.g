SIMPLEX_GetEnumerationResults:=function(n)
  local eMat, i, eDir, eFile;
  if n>7 then
    Error("Results are not known beyond dimension 7");
  fi;
  if n<=4 then
    eMat:=NullMat(n+1,n+1);
    for i in [1..+1]
    do
      eMat[i][1]:=1;
      eMat[i][i]:=1;
    od;
    return [eMat];
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/LatticeSimplices")[1];
  eFile:=Filename(eDir, Concatenation("ClassificationSimplices", String(n)));
  return ReadAsFunction(eFile)();
end;

SIMPLEX_GetInvariant:=function(EXTsimp)
  local eDet, len, ListDet, i, eDiff, EXTface, NSP, TotalBasis, ListSol;
  eDet:=AbsInt(DeterminantMat(EXTsimp));
  len:=Length(EXTsimp);
  ListDet:=[];
  for i in [1..len]
  do
    eDiff:=Difference([1..len],[i]);
    EXTface:=EXTsimp{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(EXTface));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    ListSol:=List(EXTface, x->SolutionMat(TotalBasis,x));
    Add(ListDet, AbsInt(DeterminantMat(ListSol)));
  od;
  return rec(eDet:=eDet, CollListDet:=Collected(ListDet));
end;


SIMPLEX_GetMaxDetFaces:=function(EXTsimp)
  local eDet, len, ListDet, i, eDiff, EXTface, NSP, TotalBasis, ListSol;
  len:=Length(EXTsimp);
  ListDet:=[];
  for i in [1..len]
  do
    eDiff:=Difference([1..len],[i]);
    EXTface:=EXTsimp{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(EXTface));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    ListSol:=List(EXTface, x->SolutionMat(TotalBasis,x));
    Add(ListDet, AbsInt(DeterminantMat(ListSol)));
  od;
  return Maximum(ListDet);
end;


FindLargestSpanningSimp:=function(EXT)
  local n, k, eSet, EXTface, NSP, TotalBasis, EXTfaceRed;
  if AbsInt(Determinant(EXT))=1 then
    return EXT;
  fi;
  n:=Length(EXT);
  for k in Reversed([1..n-1])
  do
    for eSet in Combinations([1..n], k)
    do
      EXTface:=EXT{eSet};
      NSP:=NullspaceIntMat(TransposedMat(EXTface));
      TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
      EXTfaceRed:=List(EXTface, x->SolutionMat(TotalBasis,x));
      if AbsInt(DeterminantMat(EXTfaceRed))=1 then
        return EXTface;
      fi;
    od;
  od;
end;



# Two Delaunay polytopes are equivalent if 
# EXT1=EXT2*A with A in AGLn(Z). But this is as sets.
# So we do all permutation of EXT1 until we find one that matches.
SIMPLEX_TestEquivalence:=function(EXT1, EXT2)
  local len, EXT2inv, eElt, EXT1perm, eMat;
  len:=Length(EXT1);
  EXT2inv:=Inverse(EXT2);
  if AbsInt(DeterminantMat(EXT1))<>AbsInt(DeterminantMat(EXT2)) then
    return false;
  fi;
  for eElt in SymmetricGroup(len)
  do
    EXT1perm:=Permuted(EXT1, eElt);
    eMat:=EXT2inv*EXT1perm;
    if IsIntegralMat(eMat) then
      return true;
    fi;
  od;
  return false;
end;


FindPositionSimplex:=function(ListSimplex, eSimplex)
  local nbSimpl, iSimp;
  nbSimpl:=Length(ListSimplex);
  for iSimp in [1..nbSimpl]
  do
    if SIMPLEX_TestEquivalence(ListSimplex[iSimp], eSimplex)=true then
      return iSimp;
    fi;
  od;
  return fail;
end;






SIMPLEX_Stabilizer:=function(EXT)
  local EXTinv, len, ListPermGen, PermGRP, ListMatrGen, MatrGRP, FuncInsert, eElt, EXTperm, eMat;
  EXTinv:=Inverse(EXT);
  len:=Length(EXT);
  ListPermGen:=[];
  PermGRP:=Group(());
  ListMatrGen:=[];
  MatrGRP:=Group([IdentityMat(len)]);
  FuncInsert:=function(eElt, eMat)
    if not(eElt in PermGRP) then
      Add(ListPermGen, eElt);
      PermGRP:=Group(ListPermGen);
      Add(ListMatrGen, eMat);
      MatrGRP:=Group(ListMatrGen);
    fi;
  end;
  for eElt in SymmetricGroup(len)
  do
    EXTperm:=Permuted(EXT, eElt);
    eMat:=EXTinv*EXTperm;
    if IsIntegralMat(eMat) then
      FuncInsert(eElt, eMat);
    fi;
  od;
  return rec(PermGRP:=PermGRP, MatrGRP:=MatrGRP);
end;




SIMPLEX_GetCharacteristicGramMatrix:=function(EXT)
  local n, nbVert, Amat, i, j, eDiffExt, eDiff, TheGram;
  n:=Length(EXT[1])-1;
  nbVert:=Length(EXT);
  Amat:=NullMat(n,n);
  for i in [1..nbVert-1]
  do
    for j in [i+1..nbVert]
    do
      eDiffExt:=EXT[i] - EXT[j];
      eDiff:=eDiffExt{[2..n+1]};
      Amat:=Amat + TransposedMat([eDiff]) * [eDiff];
    od;
  od;
  TheGram:=Inverse(Amat);
  return TheGram;
end;





SIMPLEX_ReductionByIsomorphism:=function(ListEXT)
  local ListInvariant, nbCase, ListStatus, ListNonEquiv, i, j, test;
  ListInvariant:=List(ListEXT, SIMPLEX_GetInvariant);
  nbCase:=Length(ListInvariant);
  ListStatus:=ListWithIdenticalEntries(nbCase,1);
  ListNonEquiv:=[];
  for i in [1..nbCase]
  do
    if ListStatus[i]=1 then
      Add(ListNonEquiv, ListEXT[i]);
      for j in [i+1..nbCase]
      do
        if ListStatus[j]=1 then
          if ListInvariant[i]=ListInvariant[j] then
            test:=SIMPLEX_TestEquivalence(ListEXT[i], ListEXT[j]);
            if test then
              ListStatus[j]:=0;
            fi;
          fi;
        fi;
      od;
    fi;
  od;
  return ListNonEquiv;
end;

GetSpanningFace:=function(EXTsimp)
  local len, i, eDiff, EXTface, NSP, TotalBasis, ListSol;
  len:=Length(EXTsimp);
  for i in [1..len]
  do
    eDiff:=Difference([1..len],[i]);
    EXTface:=EXTsimp{eDiff};
    NSP:=NullspaceIntMat(TransposedMat(EXTface));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
    ListSol:=List(EXTface, x->SolutionMat(TotalBasis,x));
    if AbsInt(DeterminantMat(ListSol))=1 then
      return EXTface;
    fi;
  od;
  return fail;
end;

SIMPLEX_GetBasisSpace:=function(EXT)
  local eStab, ListGen, TheBasis;
  eStab:=SIMPLEX_Stabilizer(EXT);
  Print("|GRP|=", Order(eStab.PermGRP), "\n");
  ListGen:=List(GeneratorsOfGroup(eStab.MatrGRP), x->FuncExplodeBigMatrix(x).MatrixTransformation);
  TheBasis:=InvariantFormDutourVersion(ListGen);
  Print("|TheBasis|=", Length(TheBasis), "\n");
  return TheBasis;
end;

SIMPLEX_VolumeBound:=function(n)
  return LowerInteger((2^n*Factorial(n))/NrCombinations([1..2*n],n));
end;

SIMPLEX_GetHextensionSimplex:=function(eSimplex, hIdx)
  local ListVect, i, eVect, ListCoset, ListCand, NewMat, eLine, eTrans, eCoset, n;
  n:=Length(eSimplex[1])-1;
  ListVect:=[];
  for i in [1..n]
  do
    eVect:=eSimplex[i+1]{[2..n+1]} - eSimplex[1]{[2..n+1]};
    Add(ListVect, eVect);
  od;
  ListCand:=[];
  for eVect in BuildSet(n, [0..hIdx-1])
  do
    NewMat:=[];
    for eLine in eSimplex
    do
      Add(NewMat, Concatenation(eLine, [0]));
    od;
    eTrans:=ListWithIdenticalEntries(n,0);
    for i in [1..n]
    do
      eTrans:=eTrans + eVect[i]*ListVect[i];
    od;
    Add(NewMat, Concatenation([1], eTrans, [hIdx]));
    Add(ListCand, NewMat);
  od;
  return ListCand;
end;






SIMPLEX_GetCandidatesSimplexNextDimension:=function(ListCandidatePrev)
  local ListCand, n, volBound, UpperLim, eCand, ListVect, i, eVect, ListCoset, eCoset, NewMat, eLine;
  ListCand:=[];
  n:=Length(ListCandidatePrev[1][1])-1;
  UpperLim:=SIMPLEX_VolumeBound(n+1);
  for eCand in ListCandidatePrev
  do
    ListVect:=[];
    for i in [1..n]
    do
      eVect:=eCand[i+1]{[2..n+1]} - eCand[1]{[2..n+1]};
      Add(ListVect, eVect);
    od;
    ListCoset:=GetMatrixCoset(ListVect);
    for eCoset in ListCoset
    do
      for i in [1..UpperLim]
      do
        NewMat:=[];
        for eLine in eCand
        do
          Add(NewMat, Concatenation(eLine, [0]));
        od;
        Add(NewMat, Concatenation([1], eCoset, [i]));
        if DeterminantMat(NewMat)<=volBound then
          Add(ListCand, NewMat);
        fi;
      od;
    od;
  od;
  return ListCand;
end;


SIMPLEX_TestRealizability:=function(EXT)
  local TheBasis;
  TheBasis:=SIMPLEX_GetBasisSpace(EXT);
  return TestRealizabilityDelaunay_Space(EXT, TheBasis);
end;


SIMPLEX_DetermineListAdmissibleRankOneFunction:=function(EXT)
  local n, ListContaining, eSet, fSet, eVect, eSol, aVal, gVect, TheQuadFunction, i, j, test, eRec, TheQuadFunctionRenorm, testInt, eDet, eInv, ListSets, ListVect, ListFct, ListFctProj, eRecGrp, ListPermGens, eGen, eList, GRPray, GetOrbitHypercube;
  n:=Length(EXT[1])-1;
  eDet:=AbsInt(DeterminantMat(EXT));
  eInv:=SIMPLEX_GetInvariant(EXT);
  ListSets:=[];
  ListVect:=[];
  ListFct:=[];
  ListFctProj:=[];
  for eSet in Difference(Combinations([1..n]), [ [] ])
  do
    fSet:=Difference([1..n+1], eSet);
    eVect:=ListWithIdenticalEntries(n+1,0);
    eVect{eSet}:=ListWithIdenticalEntries(Length(eSet), 1);
    eSol:=SolutionMat(TransposedMat(EXT), eVect);
    aVal:=eSol[1];
    gVect:=eSol{[2..n+1]};
    TheQuadFunction:=NullMat(n+1,n+1);
    TheQuadFunction[1][1]:=aVal*(aVal-1);
    for i in [1..n]
    do
      TheQuadFunction[1][i+1]:=(aVal-1/2)*gVect[i];
      TheQuadFunction[i+1][1]:=(aVal-1/2)*gVect[i];
    od;
    for i in [1..n]
    do
      for j in [1..n]
      do
        TheQuadFunction[i+1][j+1]:=gVect[i]*gVect[j];
      od;
    od;
    TheQuadFunctionRenorm:=RemoveFractionMatrix(TheQuadFunction);
    test:=InfDel_IsFunctionNonNegative(TheQuadFunctionRenorm);
    testInt:=IsIntegralVector(gVect);
    if test<>testInt then
      Error("Broken assumption\n");
    fi;
    if First(EXT, x->x*TheQuadFunction*x<>0)<>fail then
      Error("Critical error to resolve");
    fi;
    if test then
      Add(ListSets, eSet);
      Add(ListVect, gVect);
      Add(ListFct, TheQuadFunctionRenorm);
      Add(ListFctProj, SymmetricMatrixToVector(TheQuadFunctionRenorm));
    fi;    
  od;
  eRecGrp:=SIMPLEX_Stabilizer(EXT);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(eRec.MatrGRP)
  do
    eList:=List(ListFct, x->Position(ListFct, eGen*x*TransposedMat(eGen)));
    Add(ListPermGens, PermList(eList));
  od;
  GRPray:=Group(ListPermGens);
  GetOrbitHypercube:=function()
    local ListOrb, ListDet, eOrb, eMat, eDet;
    ListOrb:=SYMPOL_IncompleteSkeletonSearch(GRPray, ListFctProj, n);
    ListDet:=[];
    for eOrb in ListOrb
    do
      eMat:=ListVect{eOrb};
      eDet:=AbsInt(DeterminantMat(eMat));
      Add(ListDet, eDet);
    od;
    return ListDet;
  end;
  return rec(GRPray:=GRPray, 
             GetOrbitHypercube:=GetOrbitHypercube,
             ListSets:=ListSets,
             ListVect:=ListVect,
             ListFct:=ListFct,
             ListFctProj:=ListFctProj);
end;



SIMPLEX_GetNiceRepresentation_k:=function(EXT, k)
  local n, EXTred, eSet, EXTp, TheDet, TheCompl, eBasis, EXTnew, PartBasis, eDiff, ReordIdx, EXT2;
  n:=Length(EXT)-1;
  EXTred:=List(EXT, x->x{[2..n+1]} - EXT[1]{[2..n+1]});
  for eSet in Combinations([1..n+1],k)
  do
    EXTp:=EXT{eSet};
    TheDet:=GetIndexOfVectorFamily(EXTp);
    if TheDet=1 then
      EXT2:=EXTred{eSet};
      PartBasis:=List([2..k], x->EXT2[x] - EXT2[1]);
      if GetIndexOfVectorFamily(PartBasis)<>1 then
        Error("Logical problem that needs to be solvred");
      fi;
      TheCompl:=SubspaceCompletion(PartBasis, n);
      eBasis:=Concatenation([EXT[eSet[1]]], List(Concatenation(PartBasis, TheCompl), x->Concatenation([0],x)));
      if AbsInt(DeterminantMat(eBasis))<>1 then
        Error("Logical problem that needs to be solvred 2");
      fi;
      eDiff:=Difference([1..n+1], eSet);
      ReordIdx:=Concatenation(eSet, eDiff);
      EXTnew:=List(EXT{ReordIdx}, x->SolutionMat(eBasis, x));
      return EXTnew;
    fi;
  od;
  return fail;
end;

SIMPLEX_FurtherNicificationOneLine:=function(EXT)
  local n, eVect, eKey, ListVal, ListValRed, ePerm, ListValRedB, eVectB;
  n:=Length(EXT[1])-1;
  eVect:=EXT[n+1];
  eKey:=AbsInt(eVect[n+1]);
  ListVal:=eVect{[2..n]};
  ListValRed:=List(ListVal, x->x mod eKey);
  ePerm:=SortingPerm(ListValRed);
  ListValRedB:=Permuted(ListValRed, ePerm);
  eVectB:=Concatenation([1], ListValRedB, [eKey]);
  return Concatenation(EXT{[1..n]}, [eVectB]);
end;


SIMPLEX_GetNiceRepresentation:=function(EXT)
  local n, k, eReply;
  n:=Length(EXT)-1;
  for k in Reversed([1..n])
  do
    eReply:=SIMPLEX_GetNiceRepresentation_k(EXT, k);
    if eReply<>fail then
      if k=n then
        return rec(k:=k, EXT:=SIMPLEX_FurtherNicificationOneLine(eReply));
      fi;
      return rec(k:=k, EXT:=eReply);
    fi;
  od;
end;


#
# We determine the cut functions
# e(x)= (h(x) - 1) h(x)
# such that h is integral and
# 
SIMPLEX_GetCutConeOfSimplex:=function(EXT)
  local n, EXTinv, ListHvector, eSet, eVect, hVector, a, b, i, j, ListQuadFct, QuadFct, rVect;
  n:=Length(EXT[1])-1;
  EXTinv:=TransposedMat(Inverse(EXT));
  ListHvector:=[];
  ListQuadFct:=[];
  for eSet in Combinations([2..n+1])
  do
    if Length(eSet)>0 then
      eVect:=ListWithIdenticalEntries(n+1,0);
      eVect{eSet}:=ListWithIdenticalEntries(Length(eSet),1);
      hVector:=eVect*EXTinv;
      if IsIntegralVector(hVector) then
        Add(ListHvector, hVector);
        rVect:=eVect{[2..n+1]};
        a:=eVect[1];
        QuadFct:=NullMat(n+1,n+1);
        QuadFct[1][1]:=(a-1)*a;
        b:=(2*a-1)/2;
        for i in [1..n]
        do
          QuadFct[1][1+i]:=b*rVect[i];
          QuadFct[1+i][1]:=b*rVect[i];
        od;
        for i in [1..n]
        do
          for j in [1..n]
          do
            QuadFct[1+i][1+j]:=rVect[i]*rVect[j];
          od;
        od;
        Add(ListQuadFct, QuadFct);
      fi;
    fi;
  od;
  return rec(ListHvector:=ListHvector);
end;



SIMPLEX_EnumerateAffineSubspaceOfCube:=function(n)
  local PreEXT, EXT, GRP, ListRec, SaturateSet, FuncInsert, IsFinished, eSetA, eSetB, eSetC, TheStab, TheDiff, eO, O, nbRec, iRec, GetInvariant;
  PreEXT:=BuildSet(n, [0,1]);
  EXT:=List(PreEXT, x->Concatenation([1], x));
  GRP:=LinPolytope_Automorphism(EXT);
  ListRec:=[ ];
  SaturateSet:=function(eSet)
    local eSetRet, eFam, i, eSol;
    eSetRet:=[];
    eFam:=EXT{eSet};
    for i in [1..Length(EXT)]
    do
      eSol:=SolutionIntMat(eFam, EXT[i]);
      if eSol<>fail then
        Add(eSetRet, i);
      fi;
    od;
    return eSetRet;
  end;
  GetInvariant:=function(eSet)
    local ListDist, i, j, len, nb;
    ListDist:=[];
    len:=Length(eSet);
    for i in [1..len-1]
    do
      for j in [i+1..len]
      do
        nb:=Length(Filtered([1..n], x->EXT[eSet[i]]<>EXT[eSet[j]]));
        Add(ListDist, nb);
      od;
    od;
    return Collected(ListDist);
  end;
  FuncInsert:=function(eSet)
    local eRec, NewRec, eInv;
    eInv:=GetInvariant(eSet);
    for eRec in ListRec
    do
      if eRec.eInv=eInv then
        if RepresentativeAction(GRP, eRec.eSet, eSet, OnSets)<>fail then
          return;
        fi;
      fi;
    od;
    NewRec:=rec(eSet:=eSet, treated:=false, eInv:=eInv);
    Add(ListRec, NewRec);
  end;
  FuncInsert([]);
  while(true)
  do
    IsFinished:=true;
    nbRec:=Length(ListRec);
    Print("nbRec=", nbRec, "\n");
    for iRec in [1..nbRec]
    do
      if ListRec[iRec].treated=false then
        ListRec[iRec].treated:=true;
        IsFinished:=false;
        eSetA:=ListRec[iRec].eSet;
        TheStab:=Stabilizer(GRP, eSetA, OnSets);
        TheDiff:=Difference([1..Length(EXT)], eSetA);
        O:=Orbits(TheStab, TheDiff, OnPoints);
        for eO in O
        do
          eSetB:=Union(eSetA, [eO[1]]);
          eSetC:=SaturateSet(eSetB);
          FuncInsert(eSetC);
        od;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  return rec(EXT:=EXT, ListSet:=List(ListRec, x->x.eSet));
end;


SIMPLEX_GetPossibleDeterminantsFromAffineSpaces:=function(ListInfo)
  local ListSetA, EXT, EXTred, n, MinimumNumber, MinimumNumberB, ListSetB, ListSetC, eSet, O, eO, ePt, eDiff, eVect, TheSym, ListVect, nSet, ListRankOne, ListDet, EXTselection, eBasis, eDet, GRP, eStab;
  ListSetA:=ListInfo.ListSet;
  EXT:=ListInfo.EXT;
  n:=Length(EXT[1])-1;
  EXTred:=List(EXT, x->x{[2..n+1]});
  Print("|ListSetA|=", Length(ListSetA), "\n");

  MinimumNumber:=n*(n+1)/2 + 1;
  MinimumNumberB:=n*(n+1)/2;
  ListSetB:=Filtered(ListSetA, x->Length(x)>= MinimumNumber);
  Print("|ListSetB|=", Length(ListSetB), "\n");

  GRP:=LinPolytope_Automorphism(EXT);

  ListSetC:=[];
  for eSet in ListSetB
  do
    eStab:=Stabilizer(GRP, eSet, OnSets);
    O:=Orbits(eStab, eSet, OnPoints);
    for eO in O
    do
      ePt:=eO[1];
      eDiff:=Difference(eSet, [ePt]);
      eVect:=EXTred[ePt];
      TheSym:=function(h)
        local eRet, i, eVal;
        eRet:=[];
        for i in [1..n]
        do
          if eVect[i]=1 then
            eVal:=1 - h[i];
          else
            eVal:=h[i];
          fi;
          Add(eRet, eVal);
        od;
        return eRet;
      end;
      ListVect:=List(EXTred{eDiff}, TheSym);
      nSet:=Set(List(ListVect, x->Position(EXTred, x)));
      ListRankOne:=List(ListVect, x->SymmetricMatrixToVector(TransposedMat([x])*[x]));
      if RankMat(ListRankOne)=MinimumNumberB then
        Add(ListSetC, nSet);
      fi;
    od;
  od;
  Print("|ListSetC|=", Length(ListSetC), "\n");
  ListDet:=[];
  for eSet in ListSetC
  do
    EXTselection:=EXTred{eSet};
    eBasis:=BaseIntMat(EXTselection);
    eDet:=AbsInt(DeterminantMat(eBasis));
    Add(ListDet, eDet);
  od;
  Print("ListDet=", ListDet, "\n");
  return rec(ListDet:=ListDet, EXTred:=EXTred, ListSet:=ListSetC);
end;

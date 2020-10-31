#
# this is a set of functions related to Lorentzian lattice computation
# in one way or another.
LORENTZ_IsLorentzian:=function(LorMat)
  local eRec;
  eRec:=DiagonalizeSymmetricMatrix(LorMat);
  if eRec.nbPlus<>1 then
    Print("Cannot be lorentzian. Plus space should be one-dimensional\n");
    return false;
  fi;
  if eRec.nbZero<>0 then
    Print("Cannot be lorentzian. Should be nondegenerate\n");
    return false;
  fi;
  return true;
end;


LORENTZ_AssembleDiagBlocks:=function(ListMat)
  local nbMat, ListDim, TotDim, RetMat, iMat, TheShift, jMat, eDim, i, j;
  nbMat:=Length(ListMat);
  ListDim:=List(ListMat, Length);
  TotDim:=Sum(ListDim);
  RetMat:=NullMat(TotDim, TotDim);
  for iMat in [1..nbMat]
  do
    TheShift:=0;
    for jMat in [1..iMat-1]
    do
      TheShift:=TheShift + ListDim[jMat];
    od;
    eDim:=ListDim[iMat];
    for i in [1..eDim]
    do
      for j in [1..eDim]
      do
        RetMat[i+TheShift][j+TheShift]:=ListMat[iMat][i][j];
      od;
    od;
  od;
  return RetMat;
end;

#
#
# We check that all the vectors are in a plane
LORENTZ_CheckCorrectnessVectorFamily:=function(ListVect)
  local dim, ListVectExt, rnk;
  dim:=Length(ListVect[1]);
  ListVectExt:=List(ListVect, x->Concatenation([1], x));
  rnk:=RankMat(ListVectExt);
  if rnk<> dim then
    Print("We have dim=", dim, " rnk=", rnk, " they should be equal\n");
    Error("Please correct this problem");
  fi;
end;


LORENTZ_GetSpace_K3:=function(k)
  local Hmat, Smat, eMatE8, ListMat;
  Hmat:=[[0,1],
         [1,0]];
  Smat:=[[-2*k]];
  eMatE8:=ClassicalSporadicLattices("E8");
  ListMat:=[Smat, Hmat, -eMatE8, -eMatE8];
  return LORENTZ_AssembleDiagBlocks(ListMat);
end;


LORENTZ_GetTestSpace:=function(k)
  local Hmat, Smat, eMatE8, ListMat;
  Hmat:=[[0,1],
         [1,0]];
  Smat:=[[-2*k]];
  eMatE8:=ClassicalSporadicLattices("E8");
  ListMat:=[Smat, Hmat, -eMatE8];
  return LORENTZ_AssembleDiagBlocks(ListMat);
end;





#
# we enumerate all vectors having a fixed distance pattern with
# a list of vectors.
LORENTZ_ListVectorFixedDistancePattern:=function(GramMat, ListVect, DistVector)
  local n, eVect, ListVectRed, ListEqua, ListB, iVect, eDiff, eVal, ListEquaSec, ListBsec, eLine, ListEquaTot, ListBtot, MinDistPointRed, MinDistPoint, eSquareDistDiff, OneIntegralPoint, TheBasis, TheDim, AffineBasis, eCentRed, eCent, ListSolutionSet, GramMatSpec, eSolRed, eSolSpec, eSol, eDist;
  n:=Length(GramMat);
  for eVect in ListVect
  do
    if eVect[1]<>1 then
      Error("first coordinate should be 1");
    fi;
    if Length(eVect)<>n+1 then
      Error("vector length should be n+1");
    fi;
  od;
  ListVectRed:=List(ListVect, x->x{[2..n+1]});
  ListEqua:=[];
  ListB:=[];
  for iVect in [2..Length(ListVect)]
  do
    eDiff:=ListVectRed[iVect]-ListVectRed[1];
    Add(ListEqua, -2*eDiff*GramMat);
    eVal:=DistVector[iVect]-DistVector[1]-ListVectRed[iVect]*GramMat*ListVectRed[iVect]+ListVectRed[1]*GramMat*ListVectRed[1];
    Add(ListB, eVal);
  od;
  ListEquaSec:=[];
  ListBsec:=[];
  for eLine in NullspaceMat(TransposedMat(ListVect))
  do
    Add(ListEquaSec, -eLine{[2..n+1]});
    Add(ListBsec, eLine[1]);
  od;
  ListEquaTot:=Concatenation(ListEqua, ListEquaSec);
  ListBtot:=Concatenation(ListB, ListBsec);
  MinDistPointRed:=SolutionMat(TransposedMat(ListEquaTot), ListBtot);
  if MinDistPoint=fail then
    return [];
  fi;
  MinDistPoint:=Concatenation([1], MinDistPointRed);
  eDiff:=MinDistPointRed-ListVectRed[1];
  eSquareDistDiff:=DistVector[1]-eDiff*GramMat*eDiff;
  OneIntegralPoint:=SolutionIntMat(TransposedMat(ListEqua), ListB);
  TheBasis:=NullspaceIntMat(TransposedMat(ListEqua));
  TheDim:=Length(TheBasis);
  AffineBasis:=[Concatenation([1], OneIntegralPoint)];
  Append(AffineBasis, List(TheBasis, x->Concatenation([0],x)));
  eCent:=SolutionMat(AffineBasis, MinDistPoint);
  eCentRed:=eCent{[2..TheDim+1]};
  ListSolutionSet:=[];
  GramMatSpec:=TheBasis*GramMat*TransposedMat(TheBasis);
  for eSolRed in ClosestAtDistanceVallentinProgram(GramMatSpec, eCentRed, eSquareDistDiff)
  do
    eDist:=(eSolRed-eCentRed)*GramMatSpec*(eSolRed-eCentRed);
    if eDist=eSquareDistDiff then
      eSolSpec:=Concatenation([1], eSolRed);
      eSol:=eSolSpec*AffineBasis;
      Add(ListSolutionSet, eSol);
    fi;
  od;
  return ListSolutionSet;
end;





#
# We enumerate all the vectors fVect such that
# fVect * LorMat * fVect >= 0 (or =0)     and      0 < fVect * LorMat * eVect <= MaxScal
#
# TheOption can be "isotrop" or "total"
# isotrop means all the vectors that are isotrop
#
# OnlyShortest is true if we return only the vectors of minimal values fVect * LorMat * eVect
LORENTZ_FindPositiveVectors:=function(LorMat, eVect, MaxScal, TheOption, OnlyShortest)
  local eNorm, Ubasis, GramMat, TheRec, eValMax, TotalListSol, eVal, eBasSol, alpha, eTrans, eSol, eSquareDist, ListSol, eSolA, eSolB, eSolC, fScal, fNorm;
  eNorm:=eVect*LorMat*eVect;
  if TheOption<>"isotrop" and TheOption<>"total" then
    Error("AllowedValues for TheOption are isotrop or total");
  fi;
  if eNorm <= 0 then
    Error("Wrong norm of vector, will not work 1");
  fi;
  if IsIntegralVector(eVect)=false then
    Error("Vector should be integral.");
  fi;
  Ubasis:=NullspaceIntMat(TransposedMat([eVect*LorMat]));
  GramMat:=-Ubasis*LorMat*TransposedMat(Ubasis);
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("deep error");
  fi;
  TheRec:=GcdVector(eVect*LorMat);
  if TheRec.TheGcd<0 then
    Error("deep error 2");
  fi;
  eValMax:=LowerInteger(MaxScal/TheRec.TheGcd);
  TotalListSol:=[];
  for eVal in [1..eValMax]
  do
    eBasSol:=eVal*TheRec.ListCoef; # a solution of eVect * LorMat * fVect = TheGcd * eVal
    alpha:=eVal*TheRec.TheGcd/eNorm;
    eTrans:=eBasSol - alpha*eVect;
    eSol:=SolutionMat(Ubasis, eTrans);
    if eSol=fail then
      Error("Please debug from here Lorentian 1");
    fi;
    eSquareDist:=alpha*alpha*eNorm;
    ListSol:=ClosestAtDistanceVallentinProgram(GramMat, -eSol, eSquareDist);
    for eSolA in ListSol
    do
      eSolB:=eSolA*Ubasis;
      eSolC:=eBasSol+eSolB;
      fScal:=eSolC*LorMat*eVect;
      fNorm:=eSolC*LorMat*eSolC;
      if fNorm < 0 or fScal < 0 or fScal > MaxScal then
        Error("Error in norm or scalar product");
      fi;
      if IsIntegralVector(eSolC)=false then
        Error("Non integral eSolC, debug ....");
      fi;
      if TheOption="total" then
        Add(TotalListSol, eSolC);
      else
        if fNorm=0 then
          Add(TotalListSol, eSolC);
        fi;
      fi;
    od;
    if OnlyShortest and Length(TotalListSol)>0 then
      return TotalListSol;
    fi;
  od;
  return TotalListSol;
end;






LORENTZ_SearchInitialFullDim:=function(LorMat)
  local n, PosVect, MaxScal, ListPosVect, ListIsotrop, OnlyShortest;
  n:=Length(LorMat);
  PosVect:=EigenvalueFindNegativeVect(-LorMat);
  MaxScal:=PosVect*LorMat*PosVect;
  while(true)
  do
    OnlyShortest:="false";
    ListPosVect:=LORENTZ_FindPositiveVectors(LorMat, PosVect, MaxScal, "total", OnlyShortest);
    ListIsotrop:=Filtered(ListPosVect, x->x*LorMat*x=0);
    if RankMat(ListIsotrop)=n then
      break;
    fi;
    MaxScal:=MaxScal+1;
  od;
  return ListIsotrop;
end;


LORENTZ_SearchInitialIsotropSpec:=function(LorMat, PosVect)
  local n, MaxScal, ListPosVect, ListIsotrop, ListScal, eScal, eSet, OnlyShortest;
  n:=Length(LorMat);
  MaxScal:=PosVect*LorMat*PosVect;
  while(true)
  do
    OnlyShortest:=false;
    ListPosVect:=LORENTZ_FindPositiveVectors(LorMat, PosVect, MaxScal, "total", OnlyShortest);
    ListIsotrop:=Filtered(ListPosVect, x->x*LorMat*x=0);
    if Length(ListIsotrop)>0 then
      ListScal:=List(ListIsotrop, x->x*LorMat*PosVect);
      eScal:=Minimum(Difference(Set(ListScal), [0]));
      eSet:=Filtered([1..Length(ListScal)], x->ListScal[x]=eScal);
      return ListIsotrop{eSet};
    fi;
    MaxScal:=MaxScal+1;
  od;
end;

LORENTZ_SearchInitialIsotrop:=function(LorMat)
  local PosVect;
  PosVect:=EigenvalueFindNegativeVect(-LorMat);
  return LORENTZ_SearchInitialIsotropSpec(LorMat, PosVect);
end;


LORENTZ_GetDefiningIneq:=function(LorMat, ListVect)
  local nbVect, ListB, eSol;
  nbVect:=Length(ListVect);
  ListB:=ListWithIdenticalEntries(nbVect,1);
  eSol:=SolutionMat(TransposedMat(ListVect), ListB);
  return RemoveFraction(eSol*Inverse(LorMat));
end;

LORENTZ_GetDeterminingVectFamily:=function(LorMat, eFamEXT)
  local eVectDef, ListScal, MaxScal, ListVect, TheDet, AffBas, TheSel, ListCollScal, LColl, LSize, LType, nbCase, iCase, ePerm, LTypeS, ListVectB, CurrDet, eListSel, TestVect, NewDet, OnlyShortest;
  eVectDef:=LORENTZ_GetDefiningIneq(LorMat, eFamEXT);
  ListScal:=List(eFamEXT, x->x*LorMat*eVectDef);
  if Length(Set(ListScal))<>1 then
    Error("We are wrong");
  fi;
  MaxScal:=ListScal[1];
  TheDet:=AbsInt(DeterminantMat(BaseIntMat(eFamEXT)));
  if TheDet=1 then
    return eFamEXT;
  fi;
  while(true)
  do
    OnlyShortest:=false;
    ListVect:=LORENTZ_FindPositiveVectors(LorMat, eVectDef, MaxScal, "total", OnlyShortest);
    TheDet:=AbsInt(DeterminantMat(BaseIntMat(ListVect)));
    if TheDet=1 then
      AffBas:=GetZbasis(eFamEXT);
      TheSel:=Filtered(ListVect, x->SolutionIntMat(AffBas, x)=fail);
      ListCollScal:=List(TheSel, x->Collected(List(eFamEXT, y->y*LorMat*x)));
      LColl:=Collected(ListCollScal);
      LSize:=List(LColl, x->x[2]);
      LType:=List(LColl, x->x[1]);
      nbCase:=Length(LColl);
      ePerm:=SortingPerm(LSize);
      LTypeS:=Permuted(LType, ePerm);
      ListVectB:=ShallowCopy(eFamEXT);
      CurrDet:=AbsInt(DeterminantMat(BaseIntMat(eFamEXT)));
      for iCase in [1..nbCase]
      do
        eListSel:=Filtered([1..Length(TheSel)], x->ListCollScal[x]=LTypeS[iCase]);
        TestVect:=Concatenation(ListVectB, TheSel{eListSel});
        NewDet:=AbsInt(DeterminantMat(BaseIntMat(TestVect)));
        if NewDet<CurrDet then
          ListVectB:=ShallowCopy(TestVect);
          CurrDet:=NewDet;
          if CurrDet=1 then
            return ListVectB;
          fi;
        fi;
      od;
    fi;
    MaxScal:=MaxScal+1;
  od;
end;


LORENTZ_ComputeFundamentalStabInfo:=function(LorMat, eFamEXT, GRPint)
  local ListPermGen, ListMatrGenB, eGen, eMatr, GRPintMatr, phi;
  ListPermGen:=GeneratorsOfGroup(GRPint);
  ListMatrGenB:=[];
  for eGen in ListPermGen
  do
    eMatr:=FindTransformation(eFamEXT, eFamEXT, eGen);
    if IsIntegralMat(eMatr)=false then
      Error("Bug: Non integral matrix");
    fi;
    if eMatr*LorMat*TransposedMat(eMatr)<>LorMat then
      Error("Bug: eMatr does not preserve LorMat");
    fi;
    Add(ListMatrGenB, eMatr);
  od;
  GRPintMatr:=Group(ListMatrGenB);
  phi:=GroupHomomorphismByImagesNC(GRPint, GRPintMatr, ListPermGen, ListMatrGenB);
  return rec(GRP_int:=GRPint, GRPintMatr:=GRPintMatr, phi:=phi);
end;

LORENTZ_ComputeStabilizer:=function(LorMat, eFamEXT)
  local Qinv, GRPrat, ListMatrGen, test, ListVect, GRPtot, ListPermGen, ListMatrGenB, eGen, eMatr, eList, GRPint, GRPintMatr, eVect, testB, ListPGen, phi, TheStrategy;
  Qinv:=poly_private@Get_QinvMatrix(eFamEXT);
  GRPrat:=LinPolytope_AutomorphismStabSubset_AddMat(eFamEXT, eFamEXT, [Qinv, LorMat]);
  ListPGen:=GeneratorsOfGroup(GRPrat);
  ListMatrGen:=List(ListPGen, x->FindTransformation(eFamEXT, eFamEXT, x));
  test:=First(ListMatrGen, x->IsIntegralMat(x)=false);
  if test=fail then
    GRPintMatr:=Group(ListMatrGen);
    phi:=GroupHomomorphismByImagesNC(GRPrat, GRPintMatr, ListPGen, ListMatrGen);
    return rec(GRP_rat:=GRPrat, GRP_int:=GRPrat, GRPintMatr:=GRPintMatr, phi:=phi);
  fi;
  TheStrategy:=2;
  if TheStrategy=1 then
    ListVect:=LORENTZ_GetDeterminingVectFamily(LorMat, eFamEXT);
    GRPtot:=LinPolytope_AutomorphismStabSubset_AddMat(ListVect, eFamEXT, [LorMat]);
    ListPermGen:=[];
    ListMatrGenB:=[];
    for eGen in GeneratorsOfGroup(GRPtot)
    do
      eMatr:=FindTransformation(ListVect, ListVect, eGen);
      for eVect in eFamEXT*eMatr
      do
        if Position(eFamEXT, eVect)=fail then
          Error("Bug: eFamEXT vector is not invariant");
        fi;
      od;
      eList:=List(eFamEXT, x->Position(eFamEXT, x*eMatr));
      Add(ListPermGen, PermList(eList));
    od;
    GRPint:=Group(ListPermGen);
  fi;
  if TheStrategy=2 then
    GRPint:=KernelLinPolytopeIntegral_Automorphism_Subspaces(eFamEXT, GRPrat).GRPperm;
  fi;
  return LORENTZ_ComputeFundamentalStabInfo(LorMat, eFamEXT, GRPint);
end;


LORENTZ_GetAnsatzGraphInformation:=function(LorMat, eFamEXT, Qmat, HeuristicScal)
  local nbVert, ThePartition, TheListAdjacency, i, eList, j, eScal, ScalarMat, DistMat, korig, pos, LineScalar, iVert, jVert, SetV, n, SecVal;
  nbVert:=Length(eFamEXT);
  ScalarMat:=[];
  for i in [1..nbVert]
  do
    LineScalar:=[];
    for j in [1..nbVert]
    do
      eScal:=[];
      if HeuristicScal.UseLorMat then
        Add(eScal, eFamEXT[i] * LorMat * eFamEXT[j]);
      fi;
      if HeuristicScal.UseQmat then
        Add(eScal, eFamEXT[i] * Qmat * eFamEXT[j]);
      fi;
      if HeuristicScal.UseAllValues then
        Add(LineScalar, eScal);
      else
        pos:=Position(HeuristicScal.ListAllowedValues, eScal);
        Add(LineScalar, eScal);
      fi;
    od;
    Add(ScalarMat, LineScalar);
  od;
  if HeuristicScal.UseDiagonal then
    DistMat:=MappedScalarMatrixDistanceMatrix(ScalarMat);
    SetV:=__SetValue(DistMat);
    korig:=Length(SetV);
    n:=Length(DistMat);
    TheListAdjacency:=Method4modelEdgeColoredGraph(DistMat, SetV);
    ThePartition:=__Method4Partition(korig, n);
    return rec(ThePartition:=ThePartition, ListAdjacency:=TheListAdjacency);
  else
    SetV:=__SetValue(ScalarMat);
    if Length(SetV)=2 then
      SecVal:=SetV[2];
      ThePartition:=[[1..nbVert]];
      TheListAdjacency:=[];
      for iVert in [1..nbVert]
      do
        eList:=[];
        for jVert in [1..nbVert]
        do
          if iVert<>jVert then
            if ScalarMat[iVert][jVert]=SecVal then
              Add(eList, jVert);
            fi;
          fi;
        od;
        Add(TheListAdjacency, eList);
      od;
      return rec(ThePartition:=ThePartition, ListAdjacency:=TheListAdjacency);
    else
      SetV:=__SetValue(ScalarMat);
      korig:=Length(SetV);
      n:=Length(ScalarMat);
      TheListAdjacency:=Method4modelEdgeColoredGraph(ScalarMat, SetV);
      ThePartition:=__Method4Partition(korig, n);
      return rec(ThePartition:=ThePartition, ListAdjacency:=TheListAdjacency);
    fi;
  fi;
end;


LORENTZ_GetAnsatzSubpolytope:=function(LorMat, eFamEXT, Qmat, HeuristicSub)
  local nbVert, TheSub, iVert, eScal;
  nbVert:=Length(eFamEXT);
  TheSub:=[];
  for iVert in [1..nbVert]
  do
    eScal:=[];
    if HeuristicSub.UseLorMat then
      Add(eScal, eFamEXT[iVert] * LorMat * eFamEXT[iVert]);
    fi;
    if HeuristicSub.UseQmat then
      Add(eScal, eFamEXT[iVert] * Qmat * eFamEXT[iVert]);
    fi;
    if HeuristicSub.UseAllValues then
      Add(TheSub, iVert);
    else
      if Position(HeuristicSub.ListAllowedValues, eScal)<>fail then
        Add(TheSub, iVert);
      fi;
    fi;
  od;
  return TheSub;
end;




#
# This is an ansatz for specific cases.
# We have to deal with huge polytopes (2000 vertices, 5000 vertices, etc.)
# Thus what we do is reduce to a common scalar product
LORENTZ_ComputeStabilizer_Specific:=function(LorMat, eFamEXT, TheHeuristic)
  local RecAnsatz, GRPpermA, GRPpermB, GRPpermExt, Qmat, TheSub, ListMatrGens, ListPermGens;
  Qmat:=poly_private@Get_QinvMatrix(eFamEXT);
  TheSub:=LORENTZ_GetAnsatzSubpolytope(LorMat, eFamEXT, Qmat, TheHeuristic.HeuristicSub);
  RecAnsatz:=LORENTZ_GetAnsatzGraphInformation(LorMat, eFamEXT{TheSub}, Qmat, TheHeuristic.HeuristicScal);
  GRPpermA:=SymmetryGroupVertexColoredGraphAdjList(RecAnsatz.ListAdjacency, RecAnsatz.ThePartition);
  GRPpermB:=KernelLinPolytopeIntegral_Automorphism_Subspaces(eFamEXT{TheSub}, GRPpermA).GRPperm;
  ListMatrGens:=List(GeneratorsOfGroup(GRPpermB), x->FindTransformation(eFamEXT{TheSub}, eFamEXT{TheSub}, x));
  ListPermGens:=GetListPermGens(eFamEXT, ListMatrGens);
  GRPpermExt:=Group(ListPermGens);
  return LORENTZ_ComputeFundamentalStabInfo(LorMat, eFamEXT, GRPpermExt);
end;







LORENTZ_TestEquivalence_CheckAndReturn:=function(LorMat1, LorMat2, eFamEXT1, eFamEXT2, eMatrB)
  if IsIntegralMat(eMatrB)=false then
    Error("Bug: he matrix should be integral");
  fi;
  if eMatrB*LorMat1*TransposedMat(eMatrB)<>LorMat2 then
    Error("Bug: the matrix does not map the Lorentzian quadratic form");
  fi;
  if Set(eFamEXT1*eMatrB)<>Set(eFamEXT2) then
    Error("Bug: the matrix does not map the vector configurations");
  fi;
  return eMatrB;
end;


LORENTZ_TestEquivalence_General:=function(LorMat1, LorMat2, eFamEXT1, eFamEXT2)
  local Qinv1, Qinv2, eEquiv, eEquivB, eMatr, TheStrategy, ListVect1, ListVect2, eMatrB, GRP2;
  Qinv1:=poly_private@Get_QinvMatrix(eFamEXT1);
  Qinv2:=poly_private@Get_QinvMatrix(eFamEXT2);
  eEquiv:=LinPolytope_IsomorphismStabSubset_AddMat(eFamEXT1, eFamEXT1, eFamEXT2, eFamEXT2, [Qinv1, LorMat1], [Qinv2, LorMat2]);
  if eEquiv=false then
    return false;
  fi;
  eMatr:=FindTransformation(eFamEXT1, eFamEXT2, eEquiv);
  if IsIntegralMat(eMatr) and eMatr*LorMat1*TransposedMat(eMatr)=LorMat2 then
    return eMatr;
  fi;
  TheStrategy:=2;
  if TheStrategy=1 then
    ListVect1:=LORENTZ_GetDeterminingVectFamily(LorMat1, eFamEXT1);
    ListVect2:=LORENTZ_GetDeterminingVectFamily(LorMat2, eFamEXT2);
    eEquivB:=LinPolytope_IsomorphismStabSubset_AddMat(ListVect1, eFamEXT1, ListVect2, eFamEXT2, [LorMat1], [LorMat2]);
    if eEquivB=false then
      return false;
    fi;
    eMatrB:=FindTransformation(ListVect1, ListVect2, eEquivB);
  fi;
  if TheStrategy=2 then
    GRP2:=LinPolytope_AutomorphismStabSubset_AddMat(eFamEXT2, eFamEXT2, [Qinv2, LorMat2]);
    eMatrB:=KernelLinPolytopeIntegral_Isomorphism_Subspaces(eFamEXT1, eFamEXT2, GRP2, eEquiv);
    if eMatrB=false then
      return false;
    fi;
  fi;
  return LORENTZ_TestEquivalence_CheckAndReturn(LorMat1, LorMat2, eFamEXT1, eFamEXT2, eMatrB);
end;



LORENTZ_TestEquivalence_Specific:=function(LorMat1, LorMat2, eFamEXT1, eFamEXT2, TheHeuristic)
  local RecAnsatz1, RecAnsatz2, test, eMatrB, Qmat1, Qmat2, TheSub1, TheSub2;
  #
  Qmat1:=poly_private@Get_QinvMatrix(eFamEXT1);
  TheSub1:=LORENTZ_GetAnsatzSubpolytope(LorMat1, eFamEXT1, Qmat1, TheHeuristic.HeuristicSub);
  RecAnsatz1:=LORENTZ_GetAnsatzGraphInformation(LorMat1, eFamEXT1{TheSub1}, Qmat1, TheHeuristic.HeuristicScal);
  #
  Qmat2:=poly_private@Get_QinvMatrix(eFamEXT2);
  TheSub2:=LORENTZ_GetAnsatzSubpolytope(LorMat2, eFamEXT2, Qmat2, TheHeuristic.HeuristicSub);
  if Length(TheSub1)<>Length(TheSub2) then
    return false;
  fi;
  RecAnsatz2:=LORENTZ_GetAnsatzGraphInformation(LorMat2, eFamEXT2{TheSub2}, Qmat2, TheHeuristic.HeuristicScal);
  #
  if TheHeuristic.BlockMethod="PolytopeIntegral" then
    eMatrB:=LinPolytopeIntegral_Isomorphism(eFamEXT1{TheSub1}, eFamEXT2{TheSub2});
  else
    test:=EquivalenceVertexColoredGraphAdjList(RecAnsatz1.ListAdjacency, RecAnsatz2.ListAdjacency, RecAnsatz1.ThePartition);
    if test=false then
      return false;
    fi;
    eMatrB:=FindTransformation(eFamEXT1{TheSub1}, eFamEXT2{TheSub2}, PermList(test));
  fi;
  if eMatrB=false then
    return false;
  fi;
  return LORENTZ_TestEquivalence_CheckAndReturn(LorMat1, LorMat2, eFamEXT1, eFamEXT2, eMatrB);
end;



LORENTZ_TestEquivalence:=function(LorMat, eFamEXT1, eFamEXT2)
  return LORENTZ_TestEquivalence_General(LorMat, LorMat, eFamEXT1, eFamEXT2);
end;



LORENTZ_IsPerfectConf:=function(LorMat, ListVect)
  local test, n, nbVect, ListB, eSol, eVect, eNorm, ListScal, MaxScal, ListIso, ListCount, OnlyShortest;
  test:=First(ListVect, x->x*LorMat*x<>0);
  if test<>fail then
    return rec(reply:=false, reason:="Some vectors are not isotropic", eVect:=test);
  fi;
  n:=Length(LorMat);
  if RankMat(ListVect)<>n then
    return rec(reply:=false, reason:="family not of full rank", rnk:=RankMat(ListVect));
  fi;
  eVect:=LORENTZ_GetDefiningIneq(LorMat, ListVect);
  eNorm:=eVect*LorMat*eVect;
  ListScal:=List(ListVect, x->x*LorMat*eVect);
  if Length(Set(ListScal))<>1 then
    Error("Error somewhere");
  fi;
  MaxScal:=ListScal[1];
  if eNorm<=0 then
    return rec(reply:=false, reason:="Not right norm", eNorm:=eNorm);
  fi;
  OnlyShortest:=false;
  ListIso:=LORENTZ_FindPositiveVectors(LorMat, eVect, MaxScal, "total", OnlyShortest);
  ListCount:=Filtered(ListIso, x->eVect*LorMat*x<MaxScal);
  if Length(ListCount)>0 then
    return rec(reply:=false, reason:="nearer vectors", ListCount:=ListCount);
  else
    return rec(reply:=true, ListVect:=ListIso, eVect:=eVect);
  fi;
end;



LORENTZ_Kernel_Flipping:=function(LorMat, CritSet, eNSPbas, eNSPdir, TheOption)
  local n, EXT, NSP, eVert, eEXT, eNSP, NSPb, eNSPb, eNSPtest, eVectTest, MaxScal, ListTotal, EXTtest, ListIsoTest, NSPtest, eVectB, eNormTest, eVect, iShift, eMult, OnlyShortest, eDen, aShift;
  if TheOption="isotrop" then
    if First(CritSet, x->x*LorMat*x<>0)<>fail then
      Print("CritSet=", CritSet, "\n");
      Error("CritSet contains some non-isotrop vectors");
    fi;
  fi;
  n:=Length(LorMat);
  iShift:=1;
  eMult:=1;
  while(true)
  do
    eNSPtest:=eNSPbas + iShift * eMult * eNSPdir;
    eVectTest:=RemoveFraction(eNSPtest{[2..n+1]}*Inverse(LorMat));
    eNormTest:=eVectTest*LorMat*eVectTest;
    if eNormTest <= 0 then
      eMult:=eMult/2;
    else
      MaxScal:=CritSet[1]*LorMat*eVectTest;
      OnlyShortest:=true;
      ListTotal:=LORENTZ_FindPositiveVectors(LorMat, eVectTest, MaxScal, TheOption, OnlyShortest);
      if IsSubset(CritSet, Set(ListTotal)) and Length(CritSet) > Length(ListTotal) then
        Error("Here is the bug. CritSet should be ListTotal");
      fi;
      if Set(ListTotal)=CritSet then
        iShift:=iShift + 1;
      else
        if IsSubset(Set(ListTotal), CritSet) then
          return rec(ListTotal:=ListTotal, eNSPtest:=eNSPtest, eVectTest:=eVectTest, MaxScal:=MaxScal);
        else
          break;
        fi;
      fi;
    fi;
  od;
  while(true)
  do
    eVect:=ListTotal[1];
    eVert:=Concatenation([1], eVect);
    ListIsoTest:=Concatenation(CritSet, [eVect]);
    EXTtest:=List(ListIsoTest, x->Concatenation([1], x));
    aShift:=-( eNSPbas*eVert) / ( eNSPdir*eVert );
    eNSPtest:=eNSPbas + aShift*eNSPdir;
    eVectTest:=RemoveFraction(eNSPtest{[2..n+1]}*Inverse(LorMat));
    MaxScal:=CritSet[1]*LorMat*eVectTest;
    OnlyShortest:=true;
    ListTotal:=LORENTZ_FindPositiveVectors(LorMat, eVectTest, MaxScal, TheOption, OnlyShortest);
    if IsSubset(Set(ListTotal), Set(ListIsoTest)) then
      return rec(ListTotal:=ListTotal, eNSPtest:=eNSPtest, eVectTest:=eVectTest, MaxScal:=MaxScal);
    fi;
  od;
end;





LORENTZ_DoFlipping:=function(LorMat, ListIso, eInc, TheOption)
  local n, EXT, NSP, eVert, eEXT, eNSP, NSPb, eNSPb, iShift, CritSet, eNSPtest, eVectTest, MaxScal, ListTotal, EXTtest, ListIsoTest, NSPtest, eVectB, eNormTest, eNSPdir, eNSPbas, TheFlip;
  if LORENTZ_IsLorentzian(LorMat)=false then
    Error("LorMat should be Lorentzian");
  fi;
  n:=Length(LorMat);
  EXT:=List(ListIso, x->Concatenation([1], x));
  eVert:=Difference([1..Length(EXT)], eInc)[1];
  eEXT:=EXT[eVert];
  NSP:=NullspaceMat(TransposedMat(ListIso{eInc}));
  if Length(NSP)<>1 then
    Error("The array NSP should have size 1");
  fi;
  if NSP[1]*ListIso[eVert]<0 then
    eNSPdir:=RemoveFraction(Concatenation([0], -NSP[1]));
  else
    eNSPdir:=RemoveFraction(Concatenation([0],  NSP[1]));
  fi;
  NSPb:=NullspaceMat(TransposedMat(EXT));
  eVectB:=NSPb[1]{[2..n+1]};
  if eVectB*ListIso[eVert]>0 then
    eNSPbas:=RemoveFraction(NSPb[1]);
  else
    eNSPbas:=RemoveFraction(-NSPb[1]);
  fi;
  CritSet:=Set(ListIso{eInc});
  TheFlip:=LORENTZ_Kernel_Flipping(LorMat, CritSet, eNSPbas, eNSPdir, TheOption);
  LORENTZ_CheckCorrectnessVectorFamily(TheFlip.ListTotal);
  return TheFlip;
end;


LORENTZ_GetIndependentDirection:=function(LorMat, CritSet)
  local CentralVect, n, rnkCrit, a, eVect, i;
  CentralVect:=EigenvalueFindNegativeVect(-LorMat);
  n:=Length(LorMat);
  rnkCrit:=RankMat(CritSet);
  if RankMat(Concatenation(CritSet, [CentralVect]))=rnkCrit+1 then
    return CentralVect;
  fi;
  a:=2;
  while(true)
  do
    eVect:=[];
    for i in [1..n]
    do
      Add(eVect, Random([-a..a]));
    od;
    if RankMat(Concatenation(CritSet, [eVect]))=rnkCrit+1 then
      break;
    fi;
  od;
  while(true)
  do
    if eVect*LorMat*eVect>0 then
      return eVect;
    fi;
    eVect:=eVect + CentralVect;
  od;
end;


LORENTZ_PrintInfinityInformation:=function(eRecComplex)
  local	TheDim, nbPerf, nbCusp, iPerf, ListListMatch, iDim, eListMatch, iIdx, IsConjectureOk;
  TheDim:=Length(eRecComplex.ListListCells);
  nbPerf:=Length(eRecComplex.ListListCells[1]);
  nbCusp:=Length(eRecComplex.ListListCells[TheDim]);
  IsConjectureOk:=true;
  for iPerf in [1..nbPerf]
  do
    ListListMatch:=[ [iPerf] ];
    for iDim in [2..TheDim]
    do
      eListMatch:=[];
      for iIdx in ListListMatch[iDim-1]
      do
        Append(eListMatch, eRecComplex.ListListBoundary[iDim-1][iIdx].ListIFace);
      od;
      Add(ListListMatch, Set(eListMatch));
    od;
    if Length(ListListMatch[TheDim])<>nbCusp then
      IsConjectureOk:=false;
    fi;
  od;
  return IsConjectureOk;
end;


LORENTZ_PrintInfinityInformation_IsStrongCounterexample:=function(eRecComplex)
  local	TheDim, nbPerf, nbCusp, iPerf, ListListMatch, iDim, eListMatch, iIdx, IsConjectureOk, ListPerfectUnmatched, TheDiff;
  TheDim:=Length(eRecComplex.ListListCells);
  nbPerf:=Length(eRecComplex.ListListCells[1]);
  nbCusp:=Length(eRecComplex.ListListCells[TheDim]);
  ListPerfectUnmatched:=[];
  for iPerf in [1..nbPerf]
  do
    ListListMatch:=[ [iPerf] ];
    for iDim in [2..TheDim]
    do
      eListMatch:=[];
      for iIdx in ListListMatch[iDim-1]
      do
        Append(eListMatch, eRecComplex.ListListBoundary[iDim-1][iIdx].ListIFace);
      od;
      Add(ListListMatch, Set(eListMatch));
    od;
    TheDiff:=Difference([1..nbCusp], ListListMatch[TheDim]);
    Append(ListPerfectUnmatched, TheDiff);
  od;
  return Length(Set(ListPerfectUnmatched)) = nbCusp;
end;



LORENTZ_GetOnePerfect:=function(LorMat, TheOption)
  local eRec, n, pos, eVect, eScal, CritSet, eNSPbas, EXT, NSP, eVEctB, eNSPdir, eRecB, rnk, eVectB, CentralVect, IsInCone, ListNSP, ListDir;
  if LORENTZ_IsLorentzian(LorMat)=false then
    Error("LorMat should be Lorentzian");
  fi;
  IsInCone:=function(eVect)
    if eVect*LorMat*eVect<=0 then
      return false;
    fi;
    if eVect*LorMat*CentralVect <= 0 then
      return false;
    fi;
    return true;
  end;
  eRec:=DiagonalizeSymmetricMatrix(LorMat);
  n:=Length(LorMat);
  CentralVect:=EigenvalueFindNegativeVect(-LorMat);
  CritSet:=LORENTZ_SearchInitialIsotropSpec(LorMat, CentralVect);
  eScal:=CritSet[1]*LorMat*CentralVect;
  eNSPbas:=Concatenation([-eScal], CentralVect*LorMat);
  while(true)
  do
    EXT:=List(CritSet, x->Concatenation([1], x));
    NSP:=NullspaceMat(TransposedMat(EXT));
    if Length(NSP)=0 then
      return rec(ListTotal:=CritSet, eNSPtest:=eNSPbas, eVectTest:=CentralVect);
    fi;
    ListNSP:=Concatenation(NSP, -NSP);
    ListDir:=List(ListNSP, x->RemoveFraction(x{[2..n+1]}*Inverse(LorMat)));
    pos:=First([1..Length(ListDir)], x->IsInCone(ListDir[x])=false);
    eNSPdir:=ListNSP[pos];
    if First(EXT, x->x*eNSPbas<>0)<>fail then
      Error("Please debug from here Lorentzian 3");
    fi;
    eRecB:=LORENTZ_Kernel_Flipping(LorMat, CritSet, eNSPbas, eNSPdir, TheOption);
    rnk:=RankMat(eRecB.ListTotal);
    if rnk=n then
      LORENTZ_CheckCorrectnessVectorFamily(eRecB.ListTotal);
      return eRecB;
    fi;
    CritSet:=eRecB.ListTotal;
    eNSPbas:=eRecB.eNSPtest;
  od;
end;


#
# Using the ListVect, we get a slightly finer invariant.
# But the cost of computing ListVect can be tremendous, so better not to
# in general.
LORENTZ_Invariant:=function(LorMat, eFamEXT)
  return poly_private@GetScalarMatrixInvariant_PolytopeStabSubset_AddMat(eFamEXT, eFamEXT, [LorMat]);
end;




LORENTZ_EnumeratePerfect:=function(LorMat)
  local ListFamily, FuncInsertVectFamily, IsFinished, nbOrb, iOrb, ListIso, EXT, ListOrb, eOrb, ListTotal, TheGRP, eInitial, eRec, BF, DataPolyhedral, FuncStabilizer, FuncIsomorphy, FuncInvariant, IsBankSave, TmpDir, IsRespawn, WorkingDim, eAdj, ListAdj, iOrbFac, nbOrbFac, nbOrbitTreated, GetFullComplex, EXTfacet, EXTneigh;
  ListFamily:=[];
  FuncStabilizer:=LinPolytope_Automorphism;
  FuncIsomorphy:=LinPolytope_Isomorphism;
  FuncInvariant:=LinPolytope_Invariant;
  WorkingDim:=Length(LorMat);
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=WorkingDim+5 then
      return false;
    fi;
    return true;
  end;
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if OrdGRP>=50000 and TheDepth<=2 then
      return true;
    fi;
    if OrdGRP<100 then
      return false;
    fi;
    if Length(EXT)<WorkingDim+20 then
      return false;
    fi;
    if TheDepth=2 then
      return false;
    fi;
    return true;
  end;
  TmpDir:=Filename(POLYHEDRAL_tmpdir, "");
  FuncInsertVectFamily:=function(eFamEXT)
    local eRecStab, eNewRec, eFamily, test, iFamily, eInv;
    eInv:=LORENTZ_Invariant(LorMat, eFamEXT);
    for iFamily in [1..Length(ListFamily)]
    do
      if ListFamily[iFamily].eInv=eInv then
        test:=LORENTZ_TestEquivalence(LorMat, ListFamily[iFamily].eFamEXT, eFamEXT);
        if test<>false then
          return rec(iFamily:=iFamily, eEquiv:=test);
        fi;
      fi;
    od;
    eRecStab:=LORENTZ_ComputeStabilizer(LorMat, eFamEXT);
    eNewRec:=rec(eRecStab:=eRecStab, eInv:=eInv, eFamEXT:=eFamEXT, Status:="NO");
    Add(ListFamily, eNewRec);
    return rec(iFamily:=Length(ListFamily), eEquiv:=IdentityMat(Length(LorMat)));
  end;
  eInitial:=LORENTZ_GetOnePerfect(LorMat, "isotrop");
  FuncInsertVectFamily(eInitial.ListTotal);
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
        TheDepth:=0,
        IsRespawn:=IsRespawn,
        Saving:=false,
        GetInitialRays:=GetInitialRays_LinProg,
        ThePathSave:="/irrelevant/",
        ThePath:=TmpDir,
        DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction,
        GroupFormalism:=OnSetsGroupFormalism(500));
  nbOrbitTreated:=0;
  while(true)
  do
    IsFinished:=true;
    nbOrb:=Length(ListFamily);
    for iOrb in [1..nbOrb]
    do
      if ListFamily[iOrb].Status="NO" then
        ListFamily[iOrb].Status:="YES";
        IsFinished:=false;
        ListIso:=ListFamily[iOrb].eFamEXT;
        EXT:=List(ListIso, x->Concatenation([1], x));
        TheGRP:=ListFamily[iOrb].eRecStab.GRP_int;
        ListOrb:=__ListFacetByAdjacencyDecompositionMethod(EXT, TheGRP, DataPolyhedral, BF);
        nbOrbFac:=Length(ListOrb);
        ListAdj:=[];
        for iOrbFac in [1..nbOrbFac]
        do
          eOrb:=ListOrb[iOrbFac];
          EXTfacet:=ListIso{eOrb};
          eRec:=LORENTZ_DoFlipping(LorMat, ListIso, eOrb, "isotrop");
          eAdj:=FuncInsertVectFamily(eRec.ListTotal);
          EXTneigh:=ListFamily[eAdj.iFamily].eFamEXT*eAdj.eEquiv;
          if IsSubset(Set(EXTneigh), Set(EXTfacet))=false then
            Error("Inconsistency in Lorentzian neighbor facet search");
          fi;
          eAdj.eOrb:=eOrb;
          Add(ListAdj, eAdj);
        od;
        ListFamily[iOrb].ListAdj:=ListAdj;
        nbOrbitTreated:=nbOrbitTreated+1;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  GetFullComplex:=function()
    local ListListAdjInfo, eFamily, TheGRP, ListAdjInfo, nbAdj, iAdj, eAdj, RecOrb, nbEnt, iEnt, eAdjInfo, TestEquivalenceTriple, SaturationAndStabilizer, TheDim, ListCells, ListListCells, eSpMat, ListSpMat, i, iFamily, eTriple, eBasis, eRecCell, ListListBoundary, ListBoundary, GetPositionCell, eSum, ListIFace, ListElt, ListSign, ThePos, eSol, eBasisImg, TheQuot, TheSign, IsOrientable, eSet, fTriple, TheBound, nbCell1, nbCell2, ListIdx1, ListIdx2, ListEntries, ListCol, ListVal, pos, posB, eEntry, ListBoundaryImage, iFace, iCell, eGen, eMatB, eIdx, eSign, TheCoho, fRecCell;
    ListListAdjInfo:=[];
    for eFamily in ListFamily
    do
      TheGRP:=eFamily.eRecStab.GRP_int;
      ListAdjInfo:=[];
      nbAdj:=Length(eFamily.ListAdj);
      for iAdj in [1..nbAdj]
      do
        eAdj:=eFamily.ListAdj[iAdj];
        RecOrb:=OrbitWithAction(TheGRP, eAdj.eOrb, OnSets);
        nbEnt:=Length(RecOrb.ListElement);
        for iEnt in [1..nbEnt]
        do
          eAdjInfo:=rec(ePerm:=RecOrb.ListElement[iEnt], iAdj:=iAdj, eSet:=RecOrb.ListCoset[iEnt]);
          Add(ListAdjInfo, eAdjInfo);
        od;
      od;
      Add(ListListAdjInfo, ListAdjInfo);
    od;
    TestEquivalenceTriple:=function(eTriple1, eTriple2)
      local test, testMatr;
      if eTriple1.iPerfect<>eTriple2.iPerfect then
        return false;
      fi;
      test:=RepresentativeAction(ListFamily[eTriple1.iPerfect].eRecStab.GRP_int, eTriple1.eSet, eTriple2.eSet, OnSets);
      if test=fail then
        return false;
      fi;
      testMatr:=Image(ListFamily[eTriple1.iPerfect].eRecStab.phi, test);
      return Inverse(eTriple1.eMat)*testMatr*eTriple2.eMat;
    end;
    SaturationAndStabilizer:=function(eTriple)
      local ListGenStab, ListTriple, ListStatus, FuncInsert, nbTriple, IsFinished, iTriple, iPerfect, jPerfect, eSet, fSet, eMat, fMat, eMatF, EXTimg, fTriple, eBasis, FuncInsertMatrGen, TheStab, eGenMatr;
      ListGenStab:=[];
      ListTriple:=[];
      ListStatus:=[];
      EXT:=ListFamily[eTriple.iPerfect].eFamEXT{eTriple.eSet}*eTriple.eMat;
      FuncInsertMatrGen:=function(eMat)
        Add(ListGenStab, eMat);
        if First(EXT, x->Position(EXT, x*eMat)=fail)<>fail then
          Error("Clearly the generator is wrong");
        fi;
      end;
      TheStab:=Stabilizer(ListFamily[eTriple.iPerfect].eRecStab.GRP_int, eTriple.eSet, OnSets);
      for eGen in GeneratorsOfGroup(TheStab)
      do
        eGenMatr:=Image(ListFamily[eTriple.iPerfect].eRecStab.phi, eGen);
        FuncInsertMatrGen(eGenMatr);
      od;
      FuncInsert:=function(eTriple)
        local fTriple, test;
        for fTriple in ListTriple
        do
          test:=TestEquivalenceTriple(eTriple, fTriple);
          if test<>false then
            FuncInsertMatrGen(test);
            return;
          fi;
        od;
        Add(ListTriple, eTriple);
        Add(ListStatus, 1);
      end;
      FuncInsert(eTriple);
      while(true)
      do
        nbTriple:=Length(ListTriple);
        IsFinished:=true;
        for iTriple in [1..nbTriple]
        do
          if ListStatus[iTriple]=1 then
            ListStatus[iTriple]:=0;
            eTriple:=ListTriple[iTriple];
            iPerfect:=eTriple.iPerfect;
            eSet:=eTriple.eSet;
            eMat:=eTriple.eMat;
            IsFinished:=false;
            for eAdjInfo in ListListAdjInfo[iPerfect]
            do
              if IsSubset(eAdjInfo.eSet, eSet) then
                eMatF:=Image(ListFamily[iPerfect].eRecStab.phi, eAdjInfo.ePerm);
                eAdj:=ListFamily[iPerfect].ListAdj[eAdjInfo.iAdj];
                jPerfect:=eAdj.iFamily;
                fMat:=eAdj.eEquiv*eMatF*eMat;
                EXTimg:=ListFamily[jPerfect].eFamEXT*fMat;
                fSet:=Set(List(EXT, x->Position(EXTimg, x)));
                if Position(fSet, fail)<>fail then
                  Error("Equivalence matrix error");
                fi;
                fTriple:=rec(iPerfect:=jPerfect, eMat:=fMat, eSet:=fSet);
                FuncInsert(fTriple);
              fi;
            od;
          fi;
        od;
        if IsFinished=true then
          break;
        fi;
      od;
      eBasis:=RowReduction(EXT).EXT;
      return rec(ListTriple:=ListTriple, GRP:=Group(ListGenStab), eBasis:=eBasis);
    end;
    TheDim:=Length(LorMat);
    ListListCells:=[];
    ListCells:=[];
    for iFamily in [1..Length(ListFamily)]
    do
      EXT:=ListFamily[iFamily].eFamEXT;
      eTriple:=rec(iPerfect:=iFamily, eMat:=IdentityMat(TheDim), eSet:=[1..Length(EXT)]);
      eBasis:=RowReduction(EXT).EXT;
      eRecCell:=rec(ListTriple:=[eTriple], GRP:=ListFamily[iFamily].eRecStab.GRPintMatr, eBasis:=eBasis);
      Add(ListCells, eRecCell);
    od;
    Add(ListListCells, ListCells);
    ListListBoundary:=[];
    for i in [2..TheDim]
    do
      ListCells:=[];
      GetPositionCell:=function(eTriple)
        local iCell, fTriple, test;
        for iCell in [1..Length(ListCells)]
        do
          for fTriple in ListCells[iCell].ListTriple
          do
            test:=TestEquivalenceTriple(fTriple, eTriple);
            if test<>false then
              return rec(iCell:=iCell, eMat:=test);
            fi;
          od;
        od;
        eRecCell:=SaturationAndStabilizer(eTriple);
        Add(ListCells, eRecCell);
        return rec(iCell:=Length(ListCells), eMat:=IdentityMat(TheDim));
      end;
      ListBoundaryImage:=[];
      for fRecCell in ListListCells[i-1]
      do
        eTriple:=fRecCell.ListTriple[1];
        EXT:=ListFamily[eTriple.iPerfect].eFamEXT{eTriple.eSet}*eTriple.eMat;
        eSum:=Sum(EXT);
        ListIFace:=[];
        ListElt:=[];
        ListSign:=[];
        for eSet in DualDescriptionSets(EXT)
        do
          fTriple:=rec(iPerfect:=eTriple.iPerfect, eMat:=eTriple.eMat, eSet:=eTriple.eSet{eSet});
          ThePos:=GetPositionCell(fTriple);
          eBasisImg:=Concatenation(ListCells[ThePos.iCell].eBasis*ThePos.eMat, [eSum]);
          eSol:=List(eBasisImg, x->SolutionMat(fRecCell.eBasis, x));
          TheQuot:=DeterminantMat(eSol);
          if TheQuot>0 then
            TheSign:=1;
          else
            TheSign:=-1;
          fi;
          Add(ListIFace, ThePos.iCell);
          Add(ListElt, ThePos.eMat);
          Add(ListSign, TheSign);
        od;
        TheBound:=rec(ListIFace:=ListIFace, ListElt:=ListElt, ListSign:=ListSign);
        Add(ListBoundaryImage, TheBound);
      od;
      Add(ListListCells, ListCells);
      Add(ListListBoundary, ListBoundaryImage);
    od;
    for i in [1..TheDim]
    do
      for iCell in [1..Length(ListListCells[i])]
      do
        IsOrientable:=true;
        eBasis:=ListListCells[i][iCell].eBasis;
        for eGen in GeneratorsOfGroup(ListListCells[i][iCell].GRP)
        do
          eMatB:=List(eBasis, x->SolutionMat(eBasis, x*eGen));
          if DeterminantMat(eMatB)=-1 then
            IsOrientable:=false;
          fi;
        od;
        ListListCells[i][iCell].IsOrientable:=IsOrientable;
      od;
    od;
    ListSpMat:=[];
    for i in [2..TheDim]
    do
      nbCell1:=Length(ListListCells[i-1]);
      nbCell2:=Length(ListListCells[i]);
      ListIdx1:=Filtered([1..nbCell1], x->ListListCells[i-1][x].IsOrientable=true);
      ListIdx2:=Filtered([1..nbCell2], x->ListListCells[i][x].IsOrientable=true);
      ListEntries:=[];
      for eIdx in ListIdx1
      do
        TheBound:=ListListBoundary[i-1][eIdx];
        nbEnt:=Length(TheBound.ListIFace);
        ListCol:=[];
        ListVal:=[];
        for iEnt in [1..nbEnt]
        do
          iFace:=TheBound.ListIFace[iEnt];
          pos:=Position(ListIdx2, iFace);
          if pos<>fail then
            posB:=Position(ListCol, pos);
            eSign:=TheBound.ListSign[iEnt];
            if posB<>fail then
              ListVal[posB]:=ListVal[posB]+eSign;
            else
              Add(ListCol, pos);
              Add(ListVal, eSign);
            fi;
          fi;
        od;
        eEntry:=rec(ListCol:=ListCol, ListVal:=ListVal);
        Add(ListEntries, eEntry);
      od;
      eSpMat:=rec(nbLine:=Length(ListIdx1), nbCol:=Length(ListIdx2), ListEntries:=ListEntries);
      Add(ListSpMat, eSpMat);
    od;
    TheCoho:=GettingCohomologyFromSparseMatrices(ListSpMat);
    return rec(ListListCells:=ListListCells,
               ListListBoundary:=ListListBoundary,
               ListSpMat:=ListSpMat,
               TheCoho:=TheCoho);
  end;
  return rec(ListFamily:=ListFamily,
             GetFullComplex:=GetFullComplex);
end;



LORENTZ_EnumeratePerfect_DelaunayScheme:=function(LorMat, RecInput)
  local n, FuncStabilizer, FuncIsomorphy, FuncInvariant, WorkingDim, IsBankSave, IsRespawn, BF, IsSaving, MainPath, ThePathSave, ThePathTmp, PathPermanent, FindAdjacentDelaunay, KillingDelaunay, KillingAdjacency, DataLattice, DataPolyhedral, TheReply, DelaunayDatabase, EXT, eStab, FuncStabilizerDelaunay, FuncIsomorphismDelaunay, MaximalMemorySave, ListFamily, iOrb, TheRec, TheOption, ListVertAnsatz, ListAnsatzInfo;
  n:=Length(LorMat)-1;
  FuncStabilizer:=LinPolytope_Automorphism;
  FuncIsomorphy:=LinPolytope_Isomorphism;
  FuncInvariant:=LinPolytope_Invariant;
  TheOption:="isotrop";
  if IsBound(RecInput.TheOption) then
    TheOption:=RecInput.TheOption;
  fi;
  WorkingDim:=Length(LorMat);
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=WorkingDim+5 then
      return false;
    fi;
    return true;
  end;
  if IsBound(RecInput.IsBankSave) then
    IsBankSave:=RecInput.IsBankSave;
  fi;
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if OrdGRP>=50000 and TheDepth<=2 then
      return true;
    fi;
    if OrdGRP<100 then
      return false;
    fi;
    if Length(EXT)<WorkingDim+20 then
      return false;
    fi;
    if TheDepth=2 then
      return false;
    fi;
    return true;
  end;
  if IsBound(RecInput.IsRespawn) then
    IsRespawn:=RecInput.IsRespawn;
  fi;
  BF:=BankRecording(rec(Saving:=false, BankPath:="/irrelevant/"), FuncStabilizer, FuncIsomorphy, FuncInvariant, OnSetsGroupFormalism(500));
  IsSaving:=false;
  if IsBound(RecInput.IsSaving) then
    IsSaving:=RecInput.IsSaving;
  fi;
  MainPath:="/irrelevant/";
  if IsBound(RecInput.MainPath) then
    MainPath:=RecInput.MainPath;
  fi;
  ThePathSave:=Concatenation(MainPath, "Saving/");
  if MainPath<>"/irrelevant/" then
    ThePathTmp:=Concatenation(MainPath, "tmp/");
  else
    ThePathTmp:=Filename(POLYHEDRAL_tmpdir, "");
  fi;
  PathPermanent:=Concatenation(MainPath, "Permanent/");
  if IsSaving then
    Exec("mkdir -p ", ThePathTmp);
    Exec("mkdir -p ", ThePathSave);
    Exec("mkdir -p ", PathPermanent);
  fi;
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
        TheDepth:=0,
        IsRespawn:=IsRespawn,
        Saving:=IsSaving,
        GetInitialRays:=GetInitialRays_LinProg,
        ThePathSave:=ThePathSave,
        ThePath:=ThePathTmp,
        FuncStabilizer:=FuncStabilizer,
        FuncIsomorphy:=FuncIsomorphy,
        FuncInvariant:=FuncInvariant,
        DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction,
        GroupFormalism:=OnSetsGroupFormalism(500));
  #
  # The geometrical part
  #
  KillingDelaunay:=function(EXT)
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  ListAnsatzInfo:=[];
  if IsBound(RecInput.ListAnsatzInfo) then
    ListAnsatzInfo:=RecInput.ListAnsatzInfo;
  fi;
  ListVertAnsatz:=List(ListAnsatzInfo, x->x.nbVert);
  FuncStabilizerDelaunay:=function(eRec, EXT)
    local pos, RecRet;
    pos:=Position(ListVertAnsatz, Length(EXT));
    if pos<>fail then
      RecRet:=LORENTZ_ComputeStabilizer_Specific(LorMat, EXT, ListAnsatzInfo[pos].Heuristic);
    else
      RecRet:=LORENTZ_ComputeStabilizer(LorMat, EXT);
    fi;
    RecRet.PermutationStabilizer:=RecRet.GRP_int;
    return RecRet;
  end;
  FuncIsomorphismDelaunay:=function(eRec, EXT1, EXT2, eStab1)
    local pos;
    if Length(EXT1)<>Length(EXT2) then
      return false;
    fi;
    pos:=Position(ListVertAnsatz, Length(EXT1));
    if pos<>fail then
      return LORENTZ_TestEquivalence_Specific(LorMat, LorMat, EXT1, EXT2, ListAnsatzInfo[pos].Heuristic);
    else
      return LORENTZ_TestEquivalence(LorMat, EXT1, EXT2);
    fi;
  end;
  FindDelaunayPolytope:=function()
    return LORENTZ_GetOnePerfect(LorMat, TheOption).ListTotal;
  end;
  FuncInvariant:=function(eRec, EXT)
    local pos, Qmat;
    pos:=Position(ListVertAnsatz, Length(EXT));
    if pos<>fail then
      Qmat:=poly_private@Get_QinvMatrix(EXT);
      return Collected(List(EXT, x->[x*LorMat*x, x*Qmat*x]));
    else
      return LORENTZ_Invariant(LorMat, EXT);
    fi;
  end;
  FindAdjacentDelaunay:=function(EXT, eOrb)
    local ListIso, eRec;
    ListIso:=List(EXT, x->x{[2..n+1]});
    eRec:=LORENTZ_DoFlipping(LorMat, EXT, eOrb, TheOption);
    return eRec.ListTotal;
  end;
  DataLattice:=rec(n:=n,
                   Saving:=IsSaving,
		   PathPermanent:=PathPermanent,
                   KillingDelaunay:=KillingDelaunay,
                   KillingAdjacency:=KillingAdjacency,
                   FindDelaunayPolytope:=FindDelaunayPolytope,
                   FindAdjacentDelaunay:=FindAdjacentDelaunay,
                   FuncInvariant:=FuncInvariant,
		   FuncIsomorphismDelaunay:=FuncIsomorphismDelaunay,
                   FuncStabilizerDelaunay:=FuncStabilizerDelaunay);
  #
  # The saving business part
  #
  MaximalMemorySave:=IsSaving;
  DelaunayDatabase:=DelaunayDatabaseManagement(PathPermanent, IsSaving, MaximalMemorySave);
  TheReply:=ComputeDelaunayDecomposition(DataLattice, DataPolyhedral, DelaunayDatabase);
  if TheReply<>"all was ok" then
    Error("Something went wrong");
  fi;
  ListFamily:=[];
  for iOrb in [1..DelaunayDatabase.FuncDelaunayGetNumber()]
  do
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
    eStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
    TheRec:=rec(EXT:=EXT, eStab:=eStab);
    Add(ListFamily, TheRec);
  od;
  return ListFamily;
end;


LORENTZ_PrintEnumerationResult:=function(output, LorMat, ePrefix)
  local PreListSizes, PreListEXT, PreListDet, PreListInv, PreListGRP, PreListGRPsiz, ListDisc, i, eFileEXT, eFileINV, eFileGRP, EXT, eDet, eSize, eInv, eGRP, eDisc, nbCone, ePerm, ListSizes, ListEXT, ListInv, ListDet, ListGRP, ListGRPsiz, iCone, nbIso, nbNonIso, GRP_int;
  PreListSizes:=[];
  PreListEXT:=[];
  PreListDet:=[];
  PreListInv:=[];
  PreListGRP:=[];
  PreListGRPsiz:=[];
  ListDisc:=[];
  i:=1;
  while(true)
  do
    eFileEXT:=Concatenation(ePrefix, "ListEXT/DelaunayEXT", String(i));
    eFileINV:=Concatenation(ePrefix, "ListINV/DelaunayINV", String(i));
    eFileGRP:=Concatenation(ePrefix, "ListGRP/DelaunayGroup", String(i));
    if IsExistingFilePlusTouch(eFileEXT) then
      EXT:=ReadAsFunction(eFileEXT)();
      eDet:=AbsInt(DeterminantMat(BaseIntMat(EXT)));
      eSize:=Length(EXT);
      eInv:=ReadAsFunction(eFileINV)();
      eGRP:=ReadAsFunction(eFileGRP)();
      eDisc:=[1/Length(EXT), 1/Order(eGRP.GRP_int)];
      Add(PreListEXT, EXT);
      Add(PreListSizes, eSize);
      Add(PreListDet, eDet);
      Add(PreListInv, eInv);
      Add(PreListGRP, eGRP);
      Add(PreListGRPsiz, Order(eGRP.GRP_int));
      Add(ListDisc, eDisc);
    else
      break;
    fi;
    i:=i+1;
  od;
  nbCone:=Length(PreListSizes);
  ePerm:=SortingPerm(ListDisc);
  #
  ListSizes:=Permuted(PreListSizes, ePerm);
  ListEXT:=Permuted(PreListEXT, ePerm);
  ListDet:=Permuted(PreListDet, ePerm);
  ListInv:=Permuted(PreListInv, ePerm);
  ListGRP:=Permuted(PreListGRP, ePerm);
  ListGRPsiz:=Permuted(PreListGRPsiz, ePerm);
  #
  AppendTo(output, "We found ", nbCone, " perfect cones\n");
  for iCone in [1..nbCone]
  do
    EXT:=ListEXT[iCone];
    nbIso:=Length(Filtered(EXT, x->x*LorMat*x=0));
    nbNonIso:=Length(Filtered(EXT, x->x*LorMat*x>0));
    GRP_int:=ListGRP[iCone].GRP_int;
    eDet:=ListDet[iCone];
    AppendTo(output,
             "iCone=", iCone, "/", nbCone,
             " nbIso=", nbIso, " nbNonIso=", nbNonIso,
             " index=", eDet, " |GRP|=", Order(GRP_int),
      "\n");
  od;
  #
end;





LORENTZ_InvariantOfLorentzianForm:=function(LorMat)
  return DeterminantMat(LorMat);
end;

#
# It is very heavy handed (compute all perfect forms ...)
# but it works
LORENTZ_TestIsomorphismLorentzianMatrices:=function(LorMat1, LorMat2)
  local eInv1, eInv2, RecPerf, eInitial, eInvPerfect, nbFamily, iFamily, eFamEXT1, test;
  eInv1:=LORENTZ_InvariantOfLorentzianForm(LorMat1);
  eInv2:=LORENTZ_InvariantOfLorentzianForm(LorMat2);
  if eInv1<>eInv2 then
    return false;
  fi;
  RecPerf:=LORENTZ_EnumeratePerfect(LorMat1);
  eInitial:=LORENTZ_GetOnePerfect(LorMat2, "isotrop");
  eInvPerfect:=LORENTZ_Invariant(LorMat2, eInitial);
  nbFamily:=Length(RecPerf.ListFamily);
  for iFamily in [1..nbFamily]
  do
    if RecPerf.ListFamily[iFamily].eInv=eInvPerfect then
      eFamEXT1:=RecPerf.ListFamily[iFamily].eFamEXT;
      test:=LORENTZ_TestEquivalence_General(LorMat1, LorMat2, eFamEXT1, eInitial);
      if test<>false then
        if test*LorMat1*TransposedMat(test)<>LorMat2 then
          Error("The program still has some bugs");
        fi;
      fi;
    fi;
  od;
  return false;
end;





LORENTZ_ListPairScal:=function(LorMat, ListIso)
  local nbVect, ListScal, ListNb, iVect, jVect, eScal, pos;
  nbVect:=Length(ListIso);
  ListScal:=[];
  ListNb:=[];
  for iVect in [1..nbVect]
  do
    for jVect in [iVect..nbVect]
    do
      eScal:=ListIso[iVect]*LorMat*ListIso[jVect];
      pos:=Position(ListScal, eScal);
      if pos=fail then
        Add(ListScal, eScal);
        Add(ListNb, 1);
      else
        ListNb[pos]:=ListNb[pos]+1;
      fi;
    od;
  od;
  return rec(ListScal:=ListScal, ListNb:=ListNb);
end;



GetAll:=function(d)
  local PreLorMat, LorMat, LVal, i, iPerf, nbPerf, ListPerf, HMat;
  HMat:=[
[1, 0, 0, 0],
[0, 1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  PreLorMat:=NullMat(4,4);
  LVal:=[-1, -d, -1, 1];
  for i in [1..4]
  do
    PreLorMat[i][i]:=LVal[i];
  od;
  LorMat:=HMat*PreLorMat*TransposedMat(HMat);
  ListPerf:=LORENTZ_EnumeratePerfect(LorMat).ListFamily;
  nbPerf:=Length(ListPerf);
  Print("nbPerf=", nbPerf, "\n");
  for iPerf in [1..nbPerf]
  do
    Print("iPerf=", iPerf, " |EXT|=", Length(ListPerf[iPerf].eFamEXT), " |G|=", Order(ListPerf[iPerf].eRecStab.GRP_int), "\n");
  od;
  return rec(ListPerf:=ListPerf, LorMat:=LorMat, d:=d, HMat:=HMat, PreLorMat:=PreLorMat);
end;


GetAll_Sch2:=function(d)
  local PreLorMat, LorMat, LVal, i, iPerf, nbPerf, ListPerf, HMat;
  if IsInt(d/4) then
    HMat:=[
[2, 0, 0, 0],
[0, 1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  else
    HMat:=[
[1, 1, 0, 0],
[1,-1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  fi;
  PreLorMat:=NullMat(4,4);
  LVal:=[-1, -d, -1, 1];
  for i in [1..4]
  do
    PreLorMat[i][i]:=LVal[i];
  od;
  LorMat:=HMat*PreLorMat*TransposedMat(HMat);
  ListPerf:=LORENTZ_EnumeratePerfect(LorMat).ListFamily;
  nbPerf:=Length(ListPerf);
  Print("nbPerf=", nbPerf, "\n");
  for iPerf in [1..nbPerf]
  do
    Print("iPerf=", iPerf, " |EXT|=", Length(ListPerf[iPerf].eFamEXT), " |G|=", Order(ListPerf[iPerf].eRecStab.GRP_int), "\n");
  od;
  return rec(ListPerf:=ListPerf, LorMat:=LorMat, d:=d, HMat:=HMat, PreLorMat:=PreLorMat);
end;


GetAll_Sch2_complex:=function(d)
  local PreLorMat, LorMat, LVal, i, iPerf, nbPerf, ListPerf, HMat, eRec, eRecComplex;
  if IsInt(d/4) then
    HMat:=[
[2, 0, 0, 0],
[0, 1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  else
    HMat:=[
[1, 1, 0, 0],
[1,-1, 0, 0],
[0, 0, 1, 1],
[0, 0, -1,1]];
  fi;
  PreLorMat:=NullMat(4,4);
  LVal:=[-1, -d, -1, 1];
  for i in [1..4]
  do
    PreLorMat[i][i]:=LVal[i];
  od;
  LorMat:=HMat*PreLorMat*TransposedMat(HMat);
  eRec:=LORENTZ_EnumeratePerfect(LorMat);
  ListPerf:=eRec.ListFamily;
  eRecComplex:=eRec.GetFullComplex();
  nbPerf:=Length(ListPerf);
  Print("nbPerf=", nbPerf, "\n");
  for iPerf in [1..nbPerf]
  do
    Print("iPerf=", iPerf, " |EXT|=", Length(ListPerf[iPerf].eFamEXT), " |G|=", Order(ListPerf[iPerf].eRecStab.GRP_int), "\n");
  od;
  return rec(ListPerf:=ListPerf, LorMat:=LorMat, d:=d, HMat:=HMat, PreLorMat:=PreLorMat, eRecComplex:=eRecComplex);
end;





GetStrPlural:=function(nb)
  if nb=1 then
    return "";
  fi;
  return "s";
end;

G_WriteToFile:=function(FileName, TheTotalRec)
  local output, LL_EXT, L_EXT, TheDim, iRank, nbOrbit, iOrbit, eTriple, EXT, nbPerf, ListFaces, LL_ListFaces, ListPosRank, jRank, BndImg, ListOth, eEnt, L_ListFaces, d, len, pos, eRank, MatrixEdges, MatrixPoints, MatrixFaces, eSet, TheFilt, iFace, eElt, eFace, iPerf, i, eRec, PreListTrig, ListTrig, ListEList, eGen, eList, FindAdjacent, LL_Corresp, L_Corresp, eCorresp, LFaces, PrintComment, CStr, nbFacet, iFacet;
  LL_EXT:=[];
  d:=TheTotalRec.d;
  TheDim:=Length(TheTotalRec.eRecComplex.ListListCells);
  for iRank in [1..TheDim]
  do
    nbOrbit:=Length(TheTotalRec.eRecComplex.ListListCells[iRank]);
    L_EXT:=[];
    for iOrbit in [1..nbOrbit]
    do
      eTriple:=TheTotalRec.eRecComplex.ListListCells[iRank][iOrbit].ListTriple[1];
      EXT:=TheTotalRec.ListPerf[eTriple.iPerfect].eFamEXT{eTriple.eSet}*eTriple.eMat;
      Add(L_EXT, EXT);
    od;
    Add(LL_EXT, L_EXT);
  od;
  #
  LL_ListFaces:=[];
  for iRank in Reversed([1..TheDim-2])
  do
    nbOrbit:=Length(TheTotalRec.eRecComplex.ListListBoundary[iRank]);
    L_ListFaces:=[];
    for iOrbit in [1..nbOrbit]
    do
      BndImg:=TheTotalRec.eRecComplex.ListListBoundary[iRank][iOrbit];
      ListFaces:=[];
      ListPosRank:=[];
      for jRank in [iRank+1..TheDim-1]
      do
        Add(ListFaces, rec(iRank:=jRank, LFaces:=[]));
        Add(ListPosRank, jRank);
      od;
      len:=Length(BndImg.ListIFace);
      for i in [1..len]
      do
        iFace:=BndImg.ListIFace[i];
        eElt:=BndImg.ListElt[i];
        EXT:=LL_EXT[iRank+1][iFace]*eElt;
        Add(ListFaces[1].LFaces, Set(EXT));
        if iRank<TheDim-2 then
          ListOth:=LL_ListFaces[iRank+1][iFace];
          for eEnt in ListOth
          do
            eRank:=eEnt.iRank;
            pos:=Position(ListPosRank, eRank);
            for EXT in eEnt.LFaces
            do
              AddSet(ListFaces[pos].LFaces, Set(EXT*eElt));
            od;
          od;
        fi;
      od;
      Add(L_ListFaces, ListFaces);
    od;
    LL_ListFaces[iRank]:=L_ListFaces;
  od;
  FindAdjacent:=function(iPerf, eSet)
    local EXTfacet, eAdj, test, eMat, eMatB, EXTimg, pos, EXTfacetB, eRecAdj;
    EXTfacet:=TheTotalRec.ListPerf[iPerf].eFamEXT{eSet};
    for eAdj in TheTotalRec.ListPerf[iPerf].ListAdj
    do
      test:=RepresentativeAction(TheTotalRec.ListPerf[iPerf].eRecStab.GRP_int, eAdj.eOrb, eSet, OnSets);
      if test<>fail then
        eMat:=Image(TheTotalRec.ListPerf[iPerf].eRecStab.phi, test);
        eMatB:=eAdj.eEquiv*eMat;
        EXTimg:=TheTotalRec.ListPerf[eAdj.iFamily].eFamEXT*eMatB;
        if IsSubset(Set(EXTimg), Set(EXTfacet))=false then
          Error("Wrong inclusion");
        fi;
        EXTfacetB:=Set(EXTfacet*Inverse(eMatB));
        pos:=Position(LL_ListFaces[1][eAdj.iFamily][1].LFaces, EXTfacetB);
        if pos=fail then
          Error("We did not find the matching facet");
        fi;
        eRecAdj:=rec(iPerf:=eAdj.iFamily, pos:=pos, eMat:=eMatB);
        return eRecAdj;
      fi;
    od;
    Error("Failed to find entry");
  end;
  nbPerf:=Length(LL_EXT[1]);
  LL_Corresp:=[];
  for iPerf in [1..nbPerf]
  do
    L_Corresp:=[];
    EXT:=TheTotalRec.ListPerf[iPerf].eFamEXT;
    LFaces:=LL_ListFaces[1][iPerf][1].LFaces;
    for iFace in [1..Length(LFaces)]
    do
      eFace:=LFaces[iFace];
      if IsSubset(Set(EXT), Set(eFace))=false then
        Error("Inclusion error");
      fi;
      eSet:=Set(List(eFace, x->Position(EXT, x)));
      if Position(eSet, fail)<>fail then
        Error("eSet is not correct");
      fi;
      eCorresp:=FindAdjacent(iPerf, eSet);
      Add(L_Corresp, eCorresp);
    od;
    Add(LL_Corresp, L_Corresp);
  od;
  #
  RemoveFileIfExist(FileName);
  output:=OutputTextFile(FileName, true);
  if d<=10 then
    PrintComment:=true;
  else
    PrintComment:=false;
  fi;
  CStr:=function(eStr)
    if PrintComment then
      return eStr;
    else
      return "";
    fi;
  end;
  AppendTo(output, "{[", d, ",", CStr(" /* value of d */"), "\n");
  AppendTo(output, nbPerf, ",", CStr(" /* number of perfect forms */"), "\n[");
  for iPerf in [1..nbPerf]
  do
    eRec:=TheTotalRec.ListPerf[iPerf];
    EXT:=LL_EXT[1][iPerf];
    MatrixEdges:=[];
    for eFace in LL_ListFaces[1][iPerf][2].LFaces
    do
      eSet:=Set(List(eFace, x->Position(EXT, x)-1));
      Add(MatrixEdges, eSet);
    od;
    MatrixFaces:=[];
    for eFace in LL_ListFaces[1][iPerf][1].LFaces
    do
      if IsSubset(Set(EXT), Set(eFace))=false then
        Error("Inclusion error");
      fi;
      eSet:=Set(List(eFace, x->Position(EXT, x)-1));
      TheFilt:=Filtered(MatrixEdges, x->IsSubset(eSet, x));
      eFace:=ExpressPairsAsCycle(TheFilt);
      Add(MatrixFaces, eFace);
    od;
    #
    MatrixPoints:=EXT*TheTotalRec.HMat;
    #
    PreListTrig:=GetTriangulationFromLRS(MatrixPoints);
    ListTrig:=List(PreListTrig, x->x.LV);
    #
    ListEList:=[];
    for eGen in GeneratorsOfGroup(eRec.eRecStab.GRPintMatr)
    do
      eList:=List(eRec.eFamEXT, x->Position(eRec.eFamEXT, x*eGen));
      Add(ListEList, eList);
    od;
    #
    #
    #
    AppendTo(output, "[", CStr(Concatenation(" /* form number ", String(iPerf), " */")), "\n");
    AppendTo(output, CStr("/* vertices of the cone */"), "\n");
    PariB_WriteMatrix(output, MatrixPoints);
    AppendTo(output, ",\n", CStr("/* list of faces */\n"));
    PariB_WriteMatrix(output, MatrixFaces);
    AppendTo(output, ",\n", CStr("/* list of edges */\n"));
    PariB_WriteMatrix(output, MatrixEdges);
    AppendTo(output, ",\n", CStr("/* one triangulation of the cone */\n"));
    PariB_WriteMatrix(output, ListTrig);
    AppendTo(output, ",\n", CStr("/* list of generators of symmetry group*/\n"));
    PariB_WriteMatrix(output, ListEList);
    AppendTo(output, ",\n", CStr("/* size of the symmetry group */\n"));
    AppendTo(output, Order(eRec.eRecStab.GRP_int));
    AppendTo(output, ",\n", CStr("/* matching facets */\n"));
    AppendTo(output, CStr("/* iDomain, iFacet, Matrix equivalence */\n"));
    nbFacet:=Length(LL_Corresp[iPerf]);
    for iFacet in [1..nbFacet]
    do
      eCorresp:=LL_Corresp[iPerf][iFacet];
      AppendTo(output, "[", eCorresp.iPerf, ",", eCorresp.pos, ",");
      PariB_WriteMatrix(output, eCorresp.eMat);
      AppendTo(output, "]");
      if iFacet < nbFacet then
        AppendTo(output, ",\n");
      fi;
    od;
    AppendTo(output, "]");
    if iPerf < nbPerf then
      AppendTo(output, ",\n");
    fi;
  od;
  AppendTo(output, "]];}");
  CloseStream(output);
end;

PariExportResultSpecific:=function(d)
  local FileSave, RecPerf, nbPerf, AllInfoFile, output, iPerf, eRec, eStr, eSize, HMat, eMat, ListEList, PreListTrig, ListTrig, eGen, eList;
  FileSave:=Concatenation("DATAgangl/Perf_Sch2_", String(d));
  if IsExistingFilePlusTouch(FileSave)=false then
    Error("Cannot print results when we do not have them\n");
  fi;
  RecPerf:=ReadAsFunction(FileSave)();
  nbPerf:=Length(RecPerf.ListPerf);
  #
  HMat:=RecPerf.HMat;
  AllInfoFile:=Concatenation("Perfect_Pari_", String(d));
  RemoveFileIfExist(AllInfoFile);
  output:=OutputTextFile(AllInfoFile, true);
  AppendTo(output, "{[", d, ",/* value of d */\n");
  AppendTo(output, nbPerf, ", /* number of perfect forms */\n[");
  for iPerf in [1..nbPerf]
  do
    eRec:=RecPerf.ListPerf[iPerf];
    eStr:=StructureDescription(eRec.eRecStab.GRP_int);
    eSize:=Length(eRec.eFamEXT);
    eMat:=eRec.eFamEXT*HMat;
    AppendTo(output, "[");
    PariB_WriteMatrix(output, eMat);
    AppendTo(output, ",\n");
    #
    PreListTrig:=GetTriangulationFromLRS(eMat);
    ListTrig:=List(PreListTrig, x->x.LV);
    PariB_WriteMatrix(output, ListTrig);
    AppendTo(output, ",\n");
    #
    ListEList:=[];
    for eGen in GeneratorsOfGroup(eRec.eRecStab.GRPintMatr)
    do
      eList:=List(eRec.eFamEXT, x->Position(eRec.eFamEXT, x*eGen));
      Add(ListEList, eList);
    od;
    PariB_WriteMatrix(output, ListEList);
    AppendTo(output, ",", Order(eRec.eRecStab.GRP_int), "]");
    #
    if iPerf < nbPerf then
      AppendTo(output, ",\n");
    fi;
  od;
  AppendTo(output, "]];}");
  CloseStream(output);
end;







DoGlobal_PARI_out:=function(UpperBound)
  local d, FileSave, FileOut, TheTotalRec;
  for d in [2..UpperBound]
  do
    FileSave:=Concatenation("DATAgangl/Perf_Sch2_compl_", String(d));
    FileOut:=Concatenation("PariCompl/compl_", String(d));
    if IsExistingFilePlusTouch(FileSave) then
      TheTotalRec:=ReadAsFunction(FileSave)();
      RemoveFileIfExist(FileOut);
      G_WriteToFile(FileOut, TheTotalRec);
    fi;
  od;
end;



PresentResultSpecific:=function(d)
  local FileSave, RecPerf, nbPerf, AllInfoFile, output, iPerf, eRec, eStr, eSize, HMat, eMat;
  FileSave:=Concatenation("DATAgangl/Perf_Sch2_", String(d));
  if IsExistingFilePlusTouch(FileSave)=false then
    Error("Cannot print results when we do not have them\n");
  fi;
  RecPerf:=ReadAsFunction(FileSave)();
  nbPerf:=Length(RecPerf.ListPerf);
  #
  HMat:=RecPerf.HMat;
  AllInfoFile:=Concatenation("AllInfo_Sch2_", String(d));
  RemoveFileIfExist(AllInfoFile);
  output:=OutputTextFile(AllInfoFile, true);
  AppendTo(output, "Case d = ", d, "\n");
  AppendTo(output, "We have ", nbPerf, " perfect forms\n");
  for iPerf in [1..nbPerf]
  do
    eRec:=RecPerf.ListPerf[iPerf];
    eStr:=StructureDescription(eRec.eRecStab.GRP_int);
    eSize:=Length(eRec.eFamEXT);
    AppendTo(output, "Perfect form ", iPerf, " with ", eSize, " vertices and group ", eStr, "\n");
    eMat:=eRec.eFamEXT*HMat;
    WriteMatrix(output, eMat);
  od;
  CloseStream(output);
end;

GetGlobalInformation:=function()
  local FileOut, output, d, TotalListSize, TotalListGRP, FileSave, RecPerf, strPlural, eRecComplex, eEnt, nbPerf, eRec, eSize, ListPair, nb, i, eStr, ePair;
  FileOut:="ListNumberPerfect_Sch2_compl";
  RemoveFileIfExist(FileOut);
  output:=OutputTextFile(FileOut, true);
  d:=2;
  TotalListSize:=[];
  TotalListGRP:=[];
  while(true)
  do
    FileSave:=Concatenation("DATAgangl/Perf_Sch2_compl_", String(d));
    if IsExistingFilePlusTouch(FileSave) then
      RecPerf:=ReadAsFunction(FileSave)();
      nbPerf:=Length(RecPerf.ListPerf);
      ListPair:=[];
      for eRec in RecPerf.ListPerf
      do
        eStr:=StructureDescription(eRec.eRecStab.GRP_int);
        eSize:=Length(eRec.eFamEXT);
        ePair:=rec(siz:=eSize, str:=eStr);
        Add(TotalListSize, eSize);
        Add(TotalListGRP, eStr);
        Add(ListPair, ePair);
      od;
      strPlural:=GetStrPlural(nbPerf);
      AppendTo(output, "For d=", d, " we have ", nbPerf, " perfect form", strPlural, "\n");
      for eEnt in Collected(ListPair)
      do
        nb:=eEnt[2];
        strPlural:=GetStrPlural(nb);
        AppendTo(output, "  ", eEnt[2], " perfect form", strPlural);
        AppendTo(output, " with ", eEnt[1].siz, " vectors");
        AppendTo(output, " and symmetry ", eEnt[1].str, "\n");
      od;
      AppendTo(output, "  Cells of the complex\n");
      eRecComplex:=RecPerf.eRecComplex;
      for i in [1..4]
      do
        nb:=Length(eRecComplex.ListListCells[i]);
        AppendTo(output, "  For dimension ", 5-i, " we have ", nb, " cell", GetStrPlural(nb), "\n");
      od;
      AppendTo(output, "  Cohomology groups\n");
      for i in [1..Length(eRecComplex.TheCoho)]
      do
        AppendTo(output, "  H^", i, "=");
        PrintHomologyGroup(output, eRecComplex.TheCoho[i]);
        AppendTo(output, "\n");
      od;
    else
      break;
    fi;
    d:=d+1;
  od;
  #
  AppendTo(output, "Occuring for all d <= ", d-1, "\n");
  AppendTo(output, "Possible number of shortest vectors\n");
  for eEnt in Collected(TotalListSize)
  do
    nb:=eEnt[2];
    strPlural:=GetStrPlural(nb);
    AppendTo(output, eEnt[1], " vectors (", nb, " time", strPlural, ")\n");
  od;
  #
  AppendTo(output, "Possible number of symmetry groups\n");
  for eEnt in Collected(TotalListGRP)
  do
    nb:=eEnt[2];
    AppendTo(output, "group of size ", eEnt[1], "\n");
  od;
  #
  CloseStream(output);
end;

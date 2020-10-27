FileMatroidColoring:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"COLOR_MatroidLinearColorings");


Matroid_EnumerateCircuitIndependentSets:=function(EXT, GRP)
  local nbv, ListOrbitCircuit, FuncInsertCircuit, IsItCircuit, Level1list, RaiseLevel, FuncEnumerateAskedSize, ListOrbitIndependent;
  nbv:=Length(EXT);
  Level1list:=function()
    local O;
    O:=Orbits(GRP, [1..nbv], OnPoints);
    return List(O, x->[x[1]]);
  end;
  ListOrbitCircuit:=[];
  FuncInsertCircuit:=function(eCand)
    local fCand;
    for fCand in ListOrbitCircuit
    do
      if RepresentativeAction(GRP, fCand, eCand, OnSets)<>fail then
        return;
      fi;
    od;
    Add(ListOrbitCircuit, eCand);
  end;
  IsItCircuit:=function(eCand)
    local len, i, fCand;
    len:=Length(eCand);
    for i in [1..len]
    do
      fCand:=Difference(eCand, [eCand[i]]);
      if RankMat(EXT{fCand})<>len-1 then
        return false;
      fi;
    od;
    return true;
  end;
  RaiseLevel:=function(ListCandInput)
    local ListCandReturn, FuncInsert, eCand, Stab, O2, eO2, NewCand;
    ListCandReturn:=[];
    FuncInsert:=function(eCand)
      local fCand;
      for fCand in ListCandReturn
      do
        if RepresentativeAction(GRP, fCand, eCand, OnSets)<>fail then
          return;
        fi;
      od;
      Add(ListCandReturn, eCand);
    end;
    for eCand in ListCandInput
    do
      Stab:=Stabilizer(GRP, eCand, OnSets);
      O2:=Orbits(Stab, Difference([1..nbv], eCand), OnPoints);
      for eO2 in O2
      do
        NewCand:=Union(eCand, [eO2[1]]);
        if RankMat(EXT{NewCand})=Length(NewCand) then
          FuncInsert(NewCand);
        else
          if IsItCircuit(NewCand) then
            FuncInsertCircuit(NewCand);
          fi;
        fi;
      od;
    od;
    return ListCandReturn;
  end;
  FuncEnumerateAskedSize:=function(AskedSize)
    local ListReturn, TotalListReturn, iP;
    TotalListReturn:=[];
    ListReturn:=Level1list();
    Add(TotalListReturn, ListReturn);
    Print("Find ",Length(ListReturn)," orbits at step 1\n");
    for iP in [2..AskedSize]
    do
      ListReturn:=RaiseLevel(ListReturn);
      Append(TotalListReturn, ListReturn);
      Print("Find ", Length(ListReturn)," orbits at step ", iP, "\n");
    od;
    return TotalListReturn;
  end;
  ListOrbitIndependent:=FuncEnumerateAskedSize(RankMat(EXT)+1);
  return rec(ListOrbitCircuit:=ListOrbitCircuit,
             ListOrbitIndependent:=ListOrbitIndependent);
end;


Matroid_ListEdges:=function(TheGra)
  local ListEdge, n, i, j;
  ListEdge:=[];
  n:=TheGra.order;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      if IsEdge(TheGra, [i,j])=true then
        Add(ListEdge, [i,j]);
      fi;
    od;
  od;
  return ListEdge;
end;

#
# return a system with v and -v belonging to it
Matroid_AntipodalSaturation:=function(ListVect)
  local NewListVect, eVect;
  NewListVect:=[];
  for eVect in ListVect
  do
    Add(NewListVect, eVect);
    Add(NewListVect, -eVect);
  od;
  return Set(NewListVect);
end;

#
# return a system with no pairs of v, -v inside it
Matroid_AntipodalElimination:=function(ListVect)
  local nbV, ListStatus, RetList, iVect, eVect, pos;
  nbV:=Length(ListVect);
  ListStatus:=ListWithIdenticalEntries(nbV, 0);
  RetList:=[];
  for iVect in [1..nbV]
  do
    if ListStatus[iVect]=0 then
      eVect:=ListVect[iVect];
      Add(RetList, eVect);
      ListStatus[iVect]:=1;
      pos:=Position(ListVect, -eVect);
      if pos<>fail then
        ListStatus[pos]:=1;
      fi;
    fi;
  od;
  return RetList;
end;


UnimodularityInfoVectorSystem:=function(TheSystem)
  local TheSystemRed, TheSystemRed2, TheDim, ListDet, eSet, ListDet2, ListDet3, ListSet, eDet, TotalRecord, ListIdx, eMat;
  TheSystemRed:=ColumnReduction(TheSystem).EXT;
  TheSystemRed2:=Matroid_AntipodalElimination(TheSystemRed);
  TheDim:=Length(TheSystemRed[1]);
  ListDet:=[];
  ListSet:=[];
  for eSet in Combinations([1..Length(TheSystemRed2)], TheDim)
  do
    eMat:=TheSystemRed2{eSet};
    Add(ListDet, AbsInt(DeterminantMat(eMat)));
    Add(ListSet, eSet);
  od;
  ListDet2:=Set(ListDet);
  ListDet3:=Difference(ListDet2, [0]);
  TotalRecord:=[];
  for eDet in ListDet3
  do
    ListIdx:=Filtered([1..Length(ListSet)], x->ListDet[x]=eDet);
    Add(TotalRecord, rec(eDet:=eDet, ListSet:=ListSet{ListIdx}));
  od;
  return rec(EXTrel:=TheSystemRed2, TotalRecord:=TotalRecord);
end;

IsUnimodularVectorSystem:=function(TheSystem)
  return Length(UnimodularityInfoVectorSystem(TheSystem).TotalRecord)=1;
end;





Matroid_AutomorphismGroupVectorSystem:=function(ListVect)
  local ListVectRed, ListVectTot;
  ListVectRed:=ColumnReduction(ListVect).EXT;
  ListVectTot:=Matroid_AntipodalSaturation(ListVectRed);
  return __VectorConfiguration_Automorphism(ListVectTot);
end;

Matroid_AutomorphismGroupVectorSystemUnsaturated:=function(ListVect)
  local ListVectRed, ListVectTot, GRPtot, NewListPermGens, eGen, eList, eVect, pos, jpos, fVect;
  ListVectRed:=ColumnReduction(ListVect).EXT;
  ListVectTot:=Matroid_AntipodalSaturation(ListVectRed);
  GRPtot:=__VectorConfiguration_Automorphism(ListVectTot);
  NewListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRPtot)
  do
    eList:=[];
    for eVect in ListVectRed
    do
      pos:=Position(ListVectTot, eVect);
      jpos:=OnPoints(pos, eGen);
      fVect:=ListVectTot[jpos];
      pos:=Position(ListVectRed, fVect);
      if pos=fail then
        pos:=Position(ListVectRed, -fVect);
      fi;
      Add(eList, pos);
    od;
    Add(NewListPermGens, PermList(eList));
  od;
  return Group(NewListPermGens);
end;





Matroid_IsIsomorphicVectorSystem:=function(ListVect1, ListVect2)
  local ListVectRed1, ListVectTot1, ListVectRed2, ListVectTot2;
  ListVectRed1:=ColumnReduction(ListVect1).EXT;
  ListVectRed2:=ColumnReduction(ListVect2).EXT;
  ListVectTot1:=Matroid_AntipodalSaturation(ListVectRed1);
  ListVectTot2:=Matroid_AntipodalSaturation(ListVectRed2);
  return __VectorConfiguration_Isomorphism(ListVectTot1, ListVectTot2);
end;

Matroid_IsIsomorphicVectorSystemUnsaturated:=function(ListVect1, ListVect2)
  local ListVectRed1, ListVectTot1, ListVectRed2, ListVectTot2, eEquiv, NewEquiv, eVect, pos, jpos, fVect, RedPos;
  ListVectRed1:=ColumnReduction(ListVect1).EXT;
  ListVectRed2:=ColumnReduction(ListVect2).EXT;
  ListVectTot1:=Matroid_AntipodalSaturation(ListVectRed1);
  ListVectTot2:=Matroid_AntipodalSaturation(ListVectRed2);
  eEquiv:=__VectorConfiguration_Isomorphism(ListVectTot1, ListVectTot2);
  NewEquiv:=[];
  for eVect in ListVectRed1
  do
    pos:=Position(ListVectTot1, eVect);
    jpos:=eEquiv[pos];
    fVect:=ListVectTot2[jpos];
    RedPos:=Position(ListVectRed2, fVect);
    if RedPos<>fail then
      Add(NewEquiv, RedPos);
    else
      RedPos:=Position(ListVectRed2, -fVect);
      Add(NewEquiv, RedPos);
    fi;
  od;
  return NewEquiv;
end;


Matroid_GraphicVectorSystem:=function(TheGra)
  local ListVect, n, i, j, eVect, ListGraEdge, ListVectProj;
  ListVect:=[];
  ListGraEdge:=[];
  n:=TheGra.order;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      if IsEdge(TheGra, [i,j])=true then
        eVect:=ListWithIdenticalEntries(n, 0);
        eVect[i]:=1;
        eVect[j]:=-1;
        Add(ListVect, eVect);
        Add(ListGraEdge, [i,j]);
      fi;
    od;
  od;
  ListVectProj:=List(ListVect, x->x{[2..n]});
  return rec(TheSyst:=ListVect, ListVectProj:=ListVectProj, ListGraEdge:=ListGraEdge);
end;


#
# this is an attempt at implementing duality
# input system should be unimodular and in reduced form
Matroid_DualSystem:=function(TheSystem)
  local TheDim, nbVect, HRL, eSet, TheP, TheSystemIm1, Amat, H, RetMat, TheNewDim;
  TheDim:=Length(TheSystem[1]);
  nbVect:=Length(TheSystem);
  HRL:=RowReduction(TheSystem);
  eSet:=Difference([1..nbVect], HRL.Select);
  TheP:=TheSystem{HRL.Select};
  TheSystemIm1:=TheSystem*Inverse(TheP);
  Amat:=TheSystemIm1{eSet};
  H:=TransposedMat(Amat);
  RetMat:=[];
  Append(RetMat, -H);
  TheNewDim:=Length(H[1]);
  Append(RetMat, IdentityMat(TheNewDim));
  return RetMat;
end;


#
# this is a possible construction;
# we are not quite sure about what is correct definition
Matroid_CographicVectorSystem:=function(TheGra)
  local ListGraEdge, ListEqua, iVert, n, nbe, eEqua, jVert, eEdge, pos, RetMat, RetMatRed1, RetMatRed2, RetMatRed3, eDim, eVectZero;
  ListGraEdge:=Matroid_ListEdges(TheGra);
  nbe:=Length(ListGraEdge);
  n:=TheGra.order;
  ListEqua:=[];
  for iVert in [1..n]
  do
    eEqua:=ListWithIdenticalEntries(nbe, 0);
    for jVert in Adjacency(TheGra, iVert)
    do
      eEdge:=[iVert, jVert];
      pos:=Position(ListGraEdge, eEdge);
      if pos<>fail then
        eEqua[pos]:=eEqua[pos]+1;
      else
        pos:=Position(ListGraEdge, Reversed(eEdge));
        eEqua[pos]:=eEqua[pos]-1;
      fi;
    od;
    Add(ListEqua, eEqua);
  od;
  RetMat:=TransposedMat(NullspaceMat(TransposedMat(ListEqua)));
  if Length(RetMat)>0 then
    eDim:=Length(RetMat[1]);
    eVectZero:=ListWithIdenticalEntries(eDim,0);
    RetMatRed1:=Filtered(RetMat, x->x<>eVectZero);
    RetMatRed2:=List(RetMatRed1, RemoveFractionCanonic);
    RetMatRed3:=Set(RetMatRed2);
  else
    RetMatRed3:=[];
  fi;
  return rec(TheSyst:=RetMatRed3, ListGraEdge:=ListGraEdge);
end;





VectorFamilyUnsaturatedDirectSumDecomposition:=function(ListVect)
  local nbVect, GRA, GRP, FullEnum, eOrbCircuit, i;
  nbVect:=Length(ListVect);
  GRP:=Matroid_AutomorphismGroupVectorSystemUnsaturated(ListVect);
  GRA:=NullGraph(GRP, nbVect);
  FullEnum:=Matroid_EnumerateCircuitIndependentSets(ListVect, GRP);
  for eOrbCircuit in FullEnum.ListOrbitCircuit
  do
    for i in [2..Length(eOrbCircuit)]
    do
      AddEdgeOrbit(GRA, [eOrbCircuit[i],eOrbCircuit[i-1]]);
      AddEdgeOrbit(GRA, [eOrbCircuit[i-1],eOrbCircuit[i]]);
    od;
  od;
  return ConnectedComponents(GRA);
end;



Matroid_Exceptional:=function(TheName)
  local ListNames, ListEXT, iListName, eListName, pos;
  ListNames:=[];
  ListEXT:=[];
  Add(ListNames, ["E5", "R10"]);
  Add(ListEXT, 
[[0, 0, 0, 0, 1],
 [0, 0, 0, 1, 0],
 [0, 0, 1, 0, 0],
 [0, 1, 0, 0, 0],
 [1, 0, 0, 0, 0],

 [ 1, 0, 0, 1,-1],
 [ 0, 0, 1,-1, 1],
 [ 0, 1,-1, 1, 0],
 [ 1,-1, 1, 0, 0],
 [-1, 1, 0, 0, 1]]);

  Add(ListNames, ["R12"]);
  Add(ListEXT, 
[[0, 0, 0, 0, 0, 1],
 [0, 0, 0, 0, 1, 0],
 [0, 0, 0, 1, 0, 0],
 [0, 0, 1, 0, 0, 0],
 [0, 1, 0, 0, 0, 0],
 [1, 0, 0, 0, 0, 0],

 [   1,   0,   1,   1,   0,   0 ],
 [   0,   1,   1,   1,   0,   0 ],
 [   1,   0,   1,   0,   1,   1 ],
 [   0,  -1,   0,  -1,   1,   1 ],
 [   1,   0,   1,   0,   1,   0 ],
 [   0,  -1,   0,  -1,   0,   1 ] ]);
  for iListName in [1..Length(ListNames)]
  do
    eListName:=ListNames[iListName];
    pos:=Position(eListName, TheName);
    if pos<>fail then
      return ListEXT[iListName];
    fi;
  od;
  Print("ListNames=", ListNames, "\n");
  Error("Sorry, we did not find the asked matrix");
end;

EnumerateAllBasis:=function(RegMat)
  local n, nRow, ListBasis, eSet, SubMat, eDet;
  n:=Length(RegMat[1]);
  nRow:=Length(RegMat);
  ListBasis:=[];
  for eSet in Combinations([1..nRow], n)
  do
    SubMat:=RegMat{eSet};
    eDet:=DeterminantMat(SubMat);
    if eDet<>0 then
      Add(ListBasis, eSet);
    fi;
  od;
  return ListBasis;
end;



# This is the Matrix M_T in deJong paper
# It should be a projector.
Compute_CircuitOperator:=function(eMat, OneBasis)
  local nRow, M_T, eMat_Sel, iRow, eVect, eSol, i;
  nRow:=Length(eMat);
  M_T:=[];
  eMat_Sel:=eMat{OneBasis};
  for iRow in [1..nRow]
  do
    eVect:=ListWithIdenticalEntries(nRow,0);
    if Position(OneBasis, iRow)=fail then
      eSol:=SolutionMat(eMat_Sel, eMat[iRow]);
      eVect[iRow]:=1;
      for i in [1..Length(OneBasis)]
      do
        eVect[OneBasis[i]]:=-eSol[i];
      od;
      # We are a little unsure about the sign. Or for that matter
      # how the signs cancel out in the final formula
    fi;
    Add(M_T, eVect);
  od;
  return M_T;
end;


# This is the matrix N_T in deJong paper.
Compute_CocircuitOperator:=function(eMat, OneBasis)
  local n, nRow, N_T, eMat_Sel, iRow, jRow, eVect, eSol, i, pos;
  n:=Length(eMat[1]);
  nRow:=Length(eMat);
  N_T:=[];
  eMat_Sel:=eMat{OneBasis};
  for iRow in [1..nRow]
  do
    eVect:=ListWithIdenticalEntries(nRow,0);
    pos:=Position(OneBasis, iRow);
    if pos<>fail then
      for jRow in [1..nRow]
      do
        eSol:=SolutionMat(eMat_Sel, eMat[jRow]);
        eVect[jRow]:=eSol[pos];
      od;
    fi;
    Add(N_T, eVect);
  od;
  return N_T;
end;


ComputeCircuitSpace:=function(RegMat)
  return NullspaceIntMat(RegMat);
end;


ComputeCocircuitSpace:=function(RegMat)
  local IsInit, eBasis, TheImg, RedSol, MatSol, CocircuitSpace;
  IsInit:=false;
  for eBasis in EnumerateAllBasis(RegMat)
  do
    TheImg:=Compute_CocircuitOperator(RegMat, eBasis);
    if IsInit=false then
      IsInit:=true;
      CocircuitSpace:=GetZbasis(TheImg);
    else
      RedSol:=GetZbasis(TheImg);
      MatSol:=List(RedSol, x->SolutionMat(CocircuitSpace, x));
      if IsIntegralMat(MatSol)=false or AbsInt(DeterminantMat(MatSol))<>1 then
        Error("Error in our understanding of cocircuit spaces");
      fi;
    fi;
  od;
  return CocircuitSpace;
end;


Compute_w_sums:=function(ListVectorWeight, RegMat)
  local nVect, DiagMat, iVect, Gmat, eDet, TheSum, eBasis, eBasisWeight;
  nVect:=Length(RegMat);
  DiagMat:=NullMat(nVect, nVect);
  for iVect in [1..nVect]
  do
    DiagMat[iVect][iVect]:=ListVectorWeight[iVect];
  od;
  Gmat:=TransposedMat(RegMat) * DiagMat * RegMat;
  eDet:=DeterminantMat(Gmat);
  TheSum:=0;
  for eBasis in EnumerateAllBasis(RegMat)
  do
    eBasisWeight:=Product(ListVectorWeight{eBasis});
    TheSum:=TheSum + eBasisWeight;
  od;
  return TheSum;
end;



Compute_P1_P2_Projectors:=function(ListVectorWeight, RegMat)
  local sumBasisWeight, nRow, sumP1, sumP2, eBasis, eBasisWeight, M_T, N_T, P1_proj, P2_proj, ImageProj, KernelProj, eV1, eV2, eProj, ListNormProjectors, scalProd, eScal, eNorm, iRow, CircuitSpace, CocircuitSpace, eCirc, eCocirc, ComputeSpecializedSum, DiagMat, eDim, ListSums1, ListSums2, eSet, Compute_CubicalDecomposition, ComputeVectorAssignment, GetRandomVector, RegMatOr;
  eDim:=Length(RegMat[1]);
  nRow:=Length(RegMat);
  #
  # Computing Circuit and Cocircuit space
  #
  CircuitSpace:=ComputeCircuitSpace(RegMat);
  CocircuitSpace:=ComputeCocircuitSpace(RegMat);
  for eCirc in CircuitSpace
  do
    for eCocirc in CocircuitSpace
    do
      eScal:=eCirc * eCocirc;
      if eScal<>0 then
        Error("Error in scalar product of circuit and cocircuit");
      fi;
    od;
  od;
  #
  # Compute the sum_{T, S\subset T} w(T)
  #
  ComputeSpecializedSum:=function(eSet)
    local eComp, eLen, singleBasis, eBasis, RegMatRed, eVect, eSol, Gmat, eDet, CleverMethod, NaiveMethod, eBasisWeight;
    eComp:=SubspaceCompletion(RegMat{eSet}, eDim);
    eLen:=Length(eComp);
    singleBasis:=Concatenation(eComp, RegMat{eSet});
    RegMatRed:=[];
    for eVect in RegMat
    do
      eSol:=SolutionMat(singleBasis, eVect);
      Add(RegMatRed, eSol{[1..eLen]});
    od;
    DiagMat:=NullMat(nRow, nRow);
    for iRow in [1..nRow]
    do
      DiagMat[iRow][iRow]:=ListVectorWeight[iRow];
    od;
    Gmat:=TransposedMat(RegMatRed) * DiagMat * RegMatRed;
    eDet:=DeterminantMat(Gmat);
    CleverMethod:=eDet * Product(ListVectorWeight{eSet});
    #
    NaiveMethod:=0;
    for eBasis in EnumerateAllBasis(RegMat)
    do
      eBasisWeight:=Product(ListVectorWeight{eBasis});
      if IsSubset(eBasis, eSet) then
        NaiveMethod:=NaiveMethod + eBasisWeight;
      fi;
    od;
    if CleverMethod<>NaiveMethod then
      Error("Our analysis has an error somewhere");
    fi;
    return CleverMethod;
  end;
  #
  # Compute a random assignment of the vector signs
  #
  GetRandomVector:=function()
    local eVect, eFirst;
    while(true)
    do
      eVect:=List([1..eDim], x->Random([-10..10]));
      eFirst:=First(RegMat, x->x*eVect=0);
      if eFirst=fail then
        return eVect;
      fi;
    od;
  end;
  ComputeVectorAssignment:=function()
    local eVect, RegMatOr, eLine, eScal, iRow, TheSol, eDiff;
    eVect:=GetRandomVector();
    RegMatOr:=[];
    for eLine in RegMat
    do
      eScal:=eLine*eVect;
      if eScal>0 then
        Add(RegMatOr, eLine);
      else
        Add(RegMatOr, -eLine);
      fi;
    od;
    for iRow in [1..nRow]
    do
      TheSol:=SolutionMat(RegMatOr{Difference([1..nRow], [iRow])}, -RegMat[iRow]);
      if TheSol<>fail then
        eDiff:=Difference(Set(TheSol), [0,1]);
        if Length(eDiff)>0 then
          Error("We did not find a totally cyclic orientation");
        fi;
      fi;
    od;
    return RegMatOr;
  end;
  RegMatOr:=ComputeVectorAssignment();
  #
  # Compute the projectors
  #
  sumP1:=NullMat(nRow, nRow);
  sumP2:=NullMat(nRow, nRow);
  sumBasisWeight:=Compute_w_sums(ListVectorWeight, RegMat);
  for eBasis in EnumerateAllBasis(RegMat)
  do
    eBasisWeight:=Product(ListVectorWeight{eBasis});
    M_T:=Compute_CircuitOperator(RegMat, eBasis);
    N_T:=Compute_CocircuitOperator(RegMat, eBasis);
    SumMat:=M_T + TransposedMat(N_T);
    if SumMat<>IdentityMat(nRow, nRow) then
      Error("The matrix SumMat is not as we expect it to be");
    fi;
    if M_T*M_T<>M_T then
      Error("The matrix M_T is not a projector");
    fi;
    if N_T*N_T<>N_T then
      Error("The matrix N_T is not a projector");
    fi;
    sumP1:=sumP1 + eBasisWeight * M_T;
    sumP2:=sumP2 + eBasisWeight * N_T;
  od;
  P1_proj:=sumP1 / sumBasisWeight;
  P2_proj:=sumP2 / sumBasisWeight;
  Compute_CubicalDecomposition:=function()
    local ListEXT, eBasis, ListVert_C_T, eVert, i, eVect;
    ListEXT:=[];
    for eBasis in EnumerateAllBasis(RegMat)
    do
      ListVert_C_T:=[];
      for eVect in BuildSet(eDim, [-1,1])
      do
        eVert:=ListWithIdenticalEntries(eDim,0);
        for i in [1..eDim]
        do
          eVert:=eVert + sumP1[eBasis[i]] * (1/2) * eVect[i];
        od;
        Add(ListVert_C_T, eVert);
      od;
      # We need to find the translation vectors!
      Add(ListEXT, ListVert_C_T);
    od;
  end;
  if P1_proj * P1_proj<>P1_proj then
    Error("The matrix P1 is not a projector");
  fi;
  ImageProj :=GetZbasis(P1_proj);
  KernelProj:=NullspaceIntMat(RemoveFractionMatrix(P1_proj));
  # The matrix P1 is an orthogonal projector and is thus easy to compute.
  scalProd:=function(eV, fV)
    return Sum(List([1..nRow], x->eV[x] * fV[x] / ListVectorWeight[x]));
  end;
  for eV1 in ImageProj
  do
    for eV2 in KernelProj
    do
      eScal:=scalProd(eV1, eV2);
      if eScal<>0 then
        Error("The matrix P1 is not an orthogonal projector");
      fi;
    od;
  od;
  ListNormProjectors:=[];
  for iRow in [1..nRow]
  do
    eProj:=P1_proj[iRow];
    eNorm:=scalProd(eProj, eProj);
    Add(ListNormProjectors, eNorm);
  od;
  Print("ListNormProjectors=", ListNormProjectors, "\n");
  if P2_proj * P2_proj<>P2_proj then
    Error("The matrix P2 is not a projector");
  fi;
  return [P1_proj, P2_proj];
end;



GetGramMatrixSellingParameter:=function(GRA)
  local n, TheGramMat, i, eAdj, eMat;
  n:=GRA.order;
  TheGramMat:=NullMat(n,n);
  for i in [1..n]
  do
    for eAdj in Adjacency(GRA, i)
    do
      if eAdj > i then
        eMat:=NullMat(n,n);
        eMat[i][i]:=1;
        eMat[eAdj][eAdj]:=1;
        eMat[i][eAdj]:=-1;
        eMat[eAdj][i]:=-1;
	TheGramMat:=TheGramMat + eMat;
      fi;
    od;
  od;
  return List(TheGramMat{[1..n-1]}, x->x{[1..n-1]});
end;


ComputeSymbolicInfoFromGraph:=function(GRA)
  local n, ListEdge, i, eAdj, nbEdge, TheSuperbasis, eVect, pos, ListSubset, ListVector, ListSupport, eVector, eSupport, nbCase, ListRelevant, ListSub, GRAsupport, iCase, jCase, eDiff, LenLongestCycle, eSub, ListRelevantICase, ListRelevantBySubset, ListMatch, GetListLinearColoring, GetLinearChromaticNumber, ListSupportNZ;
  n:=GRA.order;
  ListEdge:=[];
  for i in [1..n]
  do
    for eAdj in Adjacency(GRA, i)
    do
      if eAdj > i then
        Add(ListEdge, [i,eAdj]);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdge);
  TheSuperbasis:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(nbEdge,0);
    for eAdj in Adjacency(GRA, i)
    do
      if eAdj>i then
        pos:=Position(ListEdge, [i, eAdj]);
	eVect[pos]:=1;
      fi;
      if eAdj<i then
        pos:=Position(ListEdge, [eAdj,i]);
	eVect[pos]:=-1;
      fi;
    od;
    Add(TheSuperbasis, eVect);
  od;
  ListSubset:=[];
  ListVector:=[];
  ListSupport:=[];
  for eSub in Combinations([1..n])
  do
    if Length(eSub)>0 then
      eVector:=Sum(TheSuperbasis{eSub});
      eSupport:=Filtered([1..nbEdge], x->eVector[x]<>0);
#      Print("eSub=", eSub, " eSupport=", eSupport, "\n");
      Add(ListSubset, eSub);
      Add(ListVector, eVector);
      Add(ListSupport, eSupport);
    fi;
  od;
  nbCase:=Length(ListSupport);
  ListSupportNZ:=Filtered(ListSupport, x->Length(x)>0);
  ListRelevant:=[];
  ListRelevantICase:=[];
  for iCase in [1..nbCase]
  do
    if ListVector[iCase]<>ListWithIdenticalEntries(n,0) then
      eSupport:=ListSupport[iCase];
      ListSub:=Filtered(ListSupportNZ, x->IsSubset(eSupport,x));
#      Print("iCase=", iCase, " eSupport=", eSupport, " |ListSub|=", Length(ListSub), "\n");
      if Length(ListSub) = 2 then
        if ListSub[1]=ListSub[2] then
          Add(ListRelevant, ListVector[iCase]);
          Add(ListRelevantICase, iCase);
        fi;
      fi;
    fi;
  od;
#  Print(NullMat(5));
  GRAsupport:=NullGraph(Group(()), nbCase);
  for iCase in [1..nbCase]
  do
    for jCase in [iCase+1..nbCase]
    do
      eDiff:=ListVector[iCase] - ListVector[jCase];
      if Position(ListRelevant, eDiff)<>fail then
        AddEdgeOrbit(GRAsupport, [iCase, jCase]);
        AddEdgeOrbit(GRAsupport, [jCase, iCase]);
      fi;
    od;
  od;
  LenLongestCycle:=Maximum(List(FindMaximalCycles(GRA), Length));
  ListRelevantBySubset:=[];
  for i in [1..n]
  do
    ListMatch:=Filtered(ListRelevantICase, x->IsSubset([1..i], ListSubset[x]) and not IsSubset([1..i-1],ListSubset[x]) );
    Add(ListRelevantBySubset, ListSubset{ListMatch});
  od;
  GetListLinearColoring:=function(nbColor)
    local FileI, FileO, output, u, len, v, eSet, siz, eVal, ListSolution;
    FileI:=Filename(POLYHEDRAL_tmpdir, "LinearColoring_in");
    FileO:=Filename(POLYHEDRAL_tmpdir, "LinearColoring_out");
    RemoveFileIfExist(FileI);
    RemoveFileIfExist(FileO);
    output:=OutputTextFile(FileI, true);
    AppendTo(output, n, "\n");
    for u in [1..n]
    do
      len:=Length(ListRelevantBySubset[u]);
      AppendTo(output, len, "\n");
      for v in [1..len]
      do
        eSet:=ListRelevantBySubset[u][v];
        siz:=Length(eSet);
	AppendTo(output, siz, "    ");
	for eVal in eSet
	do
	  AppendTo(output, " ", eVal-1);
	od;
	AppendTo(output, "\n");
      od;
    od;
    CloseStream(output);
    #
    Exec(FileMatroidColoring, " ", String(nbColor), " ", FileI, " ", FileO);
#    Print(NullMat(5));
    #
    ListSolution:=ReadAsFunction(FileO)();
    RemoveFileIfExist(FileI);
    RemoveFileIfExist(FileO);
    return ListSolution;
  end;
  GetLinearChromaticNumber:=function()
    local eChr, ListSolution;
    eChr:=2;
    while(true)
    do
      Print("Trying eChr=", eChr, "\n");
      ListSolution:=GetListLinearColoring(eChr);
      if Length(ListSolution) > 0 then
        return eChr;
      fi;
      eChr:=eChr+1;
    od;
  end;


  return rec(LenLongestCycle:=LenLongestCycle,
             GetListLinearColoring:=GetListLinearColoring,
	     GetLinearChromaticNumber:=GetLinearChromaticNumber,
             ListRelevant:=ListRelevant,
	     ListRelevantBySubset:=ListRelevantBySubset,
             GRAsupport:=GRAsupport);
end;
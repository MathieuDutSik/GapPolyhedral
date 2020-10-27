CTYP_GetLinearEqualities:=function(GramMat)
  local n, ListEqualities, eVect, ListNeigh, ListInfos, eList, eIdx1, eIdx2, eVect1, eVect2, eDiff1, eDiff2, eMatrix, eRecInfo, ListIdx, i;
  n:=Length(GramMat);
  ListEqualities:=[];
  ListInfos:=[];
  for eVect in BuildSet(n, [0,1/2])
  do
    if Sum(eVect)>0 then
      ListNeigh:=CVPVallentinProgram(GramMat, eVect).ListVect;
      eList:=List(ListNeigh, x->Position(ListNeigh, 2*eVect-x));
      ListIdx:=Filtered([1..Length(ListNeigh)], x->eList[x]>x);
      eIdx1:=ListIdx[1];
      eVect1:=ListNeigh[eIdx1];
      eDiff1:=eVect1 - eVect;
      for i in [2..Length(ListIdx)]
      do
        eIdx2:=ListIdx[i];
        eVect2:=ListNeigh[eIdx2];
        eDiff2:=eVect2 - eVect;
        eMatrix:=TransposedMat([eDiff1])*[eDiff1] - TransposedMat([eDiff2])*[eDiff2];
        eRecInfo:=rec(eVect:=eVect, eVect1:=eVect1, eVect2:=eVect2);
        Add(ListEqualities, SymmetricMatrixToVector(eMatrix));
        Add(ListInfos, eRecInfo);
      od;
    fi;
  od;
  return rec(ListEqualities:=ListEqualities,
             ListInfos:=ListInfos);
end;


CTYP_GetCtypeFromDelaunayTesselation:=function(GramMat, MatrixGRP, eCase)
  local ListIneq, TotalListMatrix, n, TheBasis, GetIneqCoefMat, FuncInsertFullOrbit, LFC, eVect, TheCVP, EXTclos, eV1, eV2, ListRec, fEXT, eMat, eRec, ListCoset;
  ListIneq:=[];
  TotalListMatrix:=[];
  n:=eCase.n;
  TheBasis:=eCase.Basis;
  GetIneqCoefMat:=function(eMatIneq)
    return List(TheBasis, x->Trace(x*eMatIneq));
  end;
  FuncInsertFullOrbit:=function(eRepIneq)
    local Lmat, ListStatus, IsFinished, len, i, nMat, eGen, FuncInsertSingle;
    if Position(ListIneq, GetIneqCoefMat(eRepIneq))<>fail then
      return;
    fi;
    Lmat:=[];
    ListStatus:=[];
    FuncInsertSingle:=function(nMat)
      Add(Lmat, nMat);
      Add(ListStatus, 0);
      Add(ListIneq, GetIneqCoefMat(nMat));
      Add(TotalListMatrix, nMat);
    end;
    FuncInsertSingle(eRepIneq);
    while(true)
    do
      IsFinished:=true;
      len:=Length(Lmat);
      for i in [1..len]
      do
        if ListStatus[i]=0 then
          ListStatus[i]:=1;
          IsFinished:=false;
          for eGen in GeneratorsOfGroup(MatrixGRP)
          do
            nMat:=TransposedMat(eGen)*Lmat[i]*eGen;
            if Position(Lmat, nMat)=fail then
              FuncInsertSingle(nMat);
            fi;
          od;
        fi;
      od;
      if IsFinished then
        break;
      fi;
    od;
#    Print("len=", len, "\n");
#    Append(TotalListMatrix, Lmat);
  end;
  LFC:=DelaunayComputationStandardFunctions(GramMat);
  ListCoset:=Filtered(BuildSet(n, [0,1/2]), x->Sum(x)>0);
  for eVect in ListCoset
  do
    TheCVP:=CVPVallentinProgram(GramMat, eVect);
    EXTclos:=List(TheCVP.ListVect, x->Concatenation([1], x));
    eV2:=EXTclos[1]{[2..n+1]} - eVect;
    ListRec:=LFC.GetAllContainingCells(eVect);
#    Print("eVect=", eVect, "\n");
#    Print("  |EXTclos|=", Length(EXTclos), " |Listrec|=", Length(ListRec), "\n");
    for eRec in ListRec
    do
      if IsSubset(Set(eRec.EXT), Set(EXTclos))=false then
        Error("EXTclos should be a subset");
      fi;
      for fEXT in Difference(Set(eRec.EXT), Set(EXTclos))
      do
        eV1:=fEXT{[2..n+1]} - eVect;
        eMat:=TransposedMat([eV1])*[eV1] - TransposedMat([eV2])*[eV2];
        FuncInsertFullOrbit(eMat);
      od;
    od;
  od;
  return rec(ListIneq:=ListIneq,
             TotalListMatrix:=TotalListMatrix);
end;


CTYP_TestUnimodularFamily:=function(ListVect)
  local ListMatrix, ListMatVect, eVect, eMat, TheSuperMat, TheFilter, ListVectTot, GRPlin, ListMatGen, eGen, TheMat, PtWiseStab, eCase, KillingDelaunay, KillingAdjacency, IsSaving, PathInitial, MatrixGRP, n, MaximalMemorySave, DelCO, TheCType, nbVect, IsCtype, iVect;
  ListMatrix:=[];
  ListMatVect:=[];
  n:=Length(ListVect[1]);
  nbVect:=Length(ListVect);
  if RankMat(ListVect)<>n then
    Error("The vector family should be full dimensional");
  fi;
  TheSuperMat:=NullMat(n,n);
  for eVect in ListVect
  do
    eMat:=TransposedMat([eVect])*[eVect];
    Add(ListMatVect, SymmetricMatrixToVector(eMat));
    Add(ListMatrix, eMat);
    TheSuperMat:=TheSuperMat + eMat;
  od;
  if RankMat(ListMatVect)<>nbVect then
    Print("For an unimodular family\n");
    Print("The complex should be simplicial\n");
    Error("Logical error");
  fi;
  TheFilter:=function(eMat)
    return true;
  end;
  ListVectTot:=Concatenation(ListVect, -ListVect);
  GRPlin:=LinPolytope_Automorphism(ListVectTot);
  ListMatGen:=[];
  for eGen in GeneratorsOfGroup(GRPlin)
  do
    TheMat:=FindTransformation(ListVectTot, ListVectTot, eGen);
    if IsIntegralMat(TheMat)=false then
      Error("The matrix should be integral by total unimodularity");
    fi;
    Add(ListMatGen, TheMat);
  od;
  PtWiseStab:=Group(ListMatGen);
  eCase:=rec(n:=n,
             Basis:=ListMatrix,
             SuperMat:=TheSuperMat,
             ScalProdMatrix:=GetScalProdMatrix(ListMatrix, TheSuperMat),
             ListComm:=[],
             TheFilter:=TheFilter,
             PtWiseStab:=PtWiseStab,
             IsAdmissible:=IsPositiveDefiniteSymmetricMatrix,
             ShortestFunction:=ShortestVectorDutourVersion);
  MatrixGRP:=ArithmeticAutomorphismGroup([TheSuperMat]);
#  KillingDelaunay:=function(EXT_Delaunay)
#    return false;
#  end;
#  KillingAdjacency:=function(EXT1, EXT2)
#    return false;
#  end;
#  MaximalMemorySave:=false;
#  IsSaving:=false;
#  PathInitial:=Filename(POLYHEDRAL_tmpdir,"");
#  DelCO:=DelaunayDescriptionStandardKernel(TheSuperMat, MatrixGRP, PathInitial, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave);
#  TheCType:=CTYP_GetCtypeFromDelaunayTesselation(DelCO, MatrixGRP, eCase);
  TheCType:=CTYP_GetCtypeFromDelaunayTesselation(TheSuperMat, MatrixGRP, eCase);
  IsCtype:=true;
  for iVect in [1..nbVect]
  do
    eVect:=ListWithIdenticalEntries(nbVect,0);
    eVect[iVect]:=1;
    if Position(TheCType.ListIneq, eVect)=fail then
      IsCtype:=false;
    fi;
  od;
  return rec(TheCType:=TheCType,
             eCase:=eCase,
             MatrixGRP:=MatrixGRP,
             IsCtype:=IsCtype);
end;



VOR_LTYPE_GetListCtypes:=function(ListConfiguration)
  local n, eCase, ListCtype, nbLtype, FuncInsert, iLtype, SumMat, eConfLtype, MatrixGRP, eConfCtype, NewMat, i, RecInfo, EXT, eEXT, SumGram, TheAct, eConfL, FuncInsertCtype;
  n:=Length(ListConfiguration[1][1]);
  eCase:=GetStandardIntegralVoronoiSpace(n);
  ListCtype:=[];
  TheAct:=function(x, g)
    return Inverse(g)*x*TransposedMat(Inverse(g));
  end;
  FuncInsertCtype:=function(iCtype, eRecL)
    local eGramMat, eVect;
    for eGramMat in eRecL.eConfL
    do
      eVect:=SymmetricMatrixToVector(eGramMat);
      if First(ListCtype[iCtype].FAC, x->x*eVect<0)<>fail then
        Error("We break the inclusion between L-type and C-type");
      fi;
    od;
    Add(ListCtype[iCtype].ListRecLtype, eRecL);
  end;
  FuncInsert:=function(eConfCtype, eConfLtype, iLtype)
    local SumGramC, SumGramL, GRP, eRecO, ListRec, iCtype, test, eRec, NewRec, SumMatB, eMat, fMat, FAC, NewRecL, ListRay, eRecL;
    SumGramC:=Sum(eConfCtype);
    SumGramL:=Sum(eConfLtype);
    GRP:=ArithmeticAutomorphismGroup([SumGramC]);
    eRecO:=OrbitWithAction(GRP, SumGramL, TheAct);
    Print("|eRecO.ListElement|=", Length(eRecO.ListElement), "\n");
    ListRec:=[];
    for eMat in eRecO.ListElement
    do
      fMat:=Inverse(eMat);
      SumMatB:=fMat*SumGramL*TransposedMat(fMat);
      eConfL:=Set(List(eConfLtype, x->fMat*x*TransposedMat(fMat)));
      NewRecL:=rec(iLtype:=iLtype, eMat:=fMat, eGramL:=SumMatB, eConfL:=eConfL);
      Add(ListRec, NewRecL);
    od;
    Print("|ListRec|=", Length(ListRec), "\n");
    for iCtype in [1..Length(ListCtype)]
    do
      test:=ArithmeticIsomorphism([SumGramC], [ListCtype[iCtype].eGram]);
      if test<>false then
        for eRec in ListRec
        do
          NewRecL:=rec(iLtype:=iLtype, eMat:=test*eRec.eMat,
                       eGramL:=test*eRec.eGramL*TransposedMat(test),
                       eConfL:=Set(List(eRec.eConfL, x->test*x*TransposedMat(test))));
          FuncInsertCtype(iCtype, NewRecL);

        od;
        return;
      fi;
    od;
    ListRay:=List(eConfCtype, SymmetricMatrixToVector);
    FAC:=DualDescription(ListRay);
    NewRec:=rec(eGram:=SumGramC, eConfCtype:=Set(eConfCtype), FAC:=FAC, ListRecLtype:=[]);
    Add(ListCtype, NewRec);
    for eRecL in ListRec
    do
      FuncInsertCtype(Length(ListCtype), eRecL);
    od;
  end;
  nbLtype:=Length(ListConfiguration);
  for iLtype in [1..nbLtype]
  do
    eConfLtype:=ListConfiguration[iLtype];
    SumGram:=Sum(eConfLtype);
    MatrixGRP:=Group([IdentityMat(n)]);
    RecInfo:=CTYP_GetCtypeFromDelaunayTesselation(SumGram, MatrixGRP, eCase);
    Print("iLtype=", iLtype, "\n");
    EXT:=DualDescription(RecInfo.ListIneq);
    eConfCtype:=[];
    for eEXT in EXT
    do
      NewMat:=[];
      for i in [1..Length(eCase.Basis)]
      do
        NewMat:=NewMat + eCase.Basis[i]*eEXT[i];
      od;
      Add(eConfCtype, RemoveFractionMatrix(NewMat));
    od;
    FuncInsert(eConfCtype, eConfLtype, iLtype);
  od;
  return ListCtype;
end;



CTYP_GetBasis:=function(n)
  local ListSymmMat, i, TMat, j;
  ListSymmMat:=[];
  for i in [1..n]
  do
    TMat:=NullMat(n,n);
    TMat[i][i]:=1;
    Add(ListSymmMat, TMat);
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      TMat:=NullMat(n,n);
      TMat[i][j]:=1;
      TMat[j][i]:=1;
      Add(ListSymmMat, TMat);
    od;
  od;
  return ListSymmMat;
end;



CTYP_GetCtypeFromLtype:=function(OneLtype, TheGroup)
  local n, ListEdges, eDelaunay, EXT, LAdj, iVert, jVert, eDiff, ListReturnEdges, eVect, TheOrb;
  n:=Length(OneLtype[1].EXT[1])-1;
  ListEdges:=[];
  for eDelaunay in OneLtype
  do
    EXT:=eDelaunay.EXT;
    LAdj:=AdjacencyComputation(EXT);
    for iVert in [1..Length(EXT)]
    do
      for jVert in LAdj[iVert]
      do
        eDiff:=EXT[iVert]-EXT[jVert];
        Add(ListEdges, eDiff{[2..n+1]});
      od;
    od;
  od;
  ListEdges:=Set(ListEdges);
  ListReturnEdges:=[];
  while(true)
  do
    if Length(ListEdges)=0 then
      break;
    fi;
    eVect:=ListEdges[1];
    TheOrb:=Orbit(TheGroup, eVect);
    Append(ListReturnEdges, TheOrb);
    ListEdges:=Difference(ListEdges, Set(TheOrb));
  od;
  return ListReturnEdges;
end;



CTYP_GetFreeVectors:=function(TheCtype)
  local n, ListFreeVect, eVect, ListEven;
  n:=Length(TheCtype[1]);
  ListFreeVect:=[];
  for eVect in BuildSet(n, [0,1])
  do
    ListEven:=Filtered(TheCtype, x-> (x*eVect) mod 2 = 0);
    if RankMat(ListEven)=n-1 then
      Add(ListFreeVect, eVect);
    fi;
  od;
  return ListFreeVect;
end;



CTYP_GetListTriples:=function(TheCtype)
  local nbEdge, ListTriples, i, j, eDiff, pos;
  nbEdge:=Length(TheCtype);
  ListTriples:=[];
  for i in [1..nbEdge-1]
  do
    for j in [i+1..nbEdge]
    do
      eDiff:=-TheCtype[i]-TheCtype[j];
      pos:=Position(TheCtype, eDiff);
      if pos<>fail then
        Add(ListTriples, Set([i,j, pos]));
      fi;
    od;
  od;
  return Set(ListTriples);
end;


CTYP_GetInequalitiesOfCtype:=function(TheCtype, TheBasis, n)
  local ListTriples, ListInequalities, ListInformations, FuncInsertInequality, eTriple, ListInequalitiesRed, ListPos, i, iN1, iN2, iEdge, nbEdge, ListListVect, rnk;
  ListTriples:=CTYP_GetListTriples(TheCtype);
  ListInequalities:=[];
  ListInformations:=[];
  FuncInsertInequality:=function(i, j, k)
    local TheVector, uVec, wVec, eMat, TheVectorRed, pos, TheInfo;
    TheVector:=[];
    uVec:=TheCtype[i];
    wVec:=TheCtype[k];
    for eMat in TheBasis
    do
      Add(TheVector, (-wVec-uVec/2)*eMat*(-wVec-uVec/2) - uVec*eMat*uVec/4);
    od;
    TheVectorRed:=RemoveFraction(TheVector);
    pos:=Position(ListInequalities, TheVectorRed);
    TheInfo:=[i, [j,k]];
    if pos=fail then
      Add(ListInequalities, TheVectorRed);
      Add(ListInformations, [TheInfo]);
    else
      Add(ListInformations[pos], TheInfo);
    fi;
  end;
  nbEdge:=Length(TheCtype);
  ListListVect:=[];
  for iEdge in [1..nbEdge]
  do
    Add(ListListVect, []);
  od;
  for eTriple in ListTriples
  do
    for i in [1..3]
    do
      iN1:=NextIdx(3,i);
      iN2:=NextIdx(3,iN1);
      FuncInsertInequality(eTriple[i], eTriple[iN1], eTriple[iN2]);
      Append(ListListVect[eTriple[i]], [eTriple[iN1], eTriple[iN2]]);
    od;
  od;
  for iEdge in [1..nbEdge]
  do
    rnk:=RankMat(TheCtype{ListListVect[iEdge]});
#    Print("iEdge=", iEdge, " rnk=", rnk, "\n");
  od;


#  Print("Inequalities generated, |Ineq|=", Length(ListInequalities), "\n");
  return rec(ListInequalities:=ListInequalities, ListInformations:=ListInformations, TheCtype:=TheCtype);
end;



CTYP_TheFlipping:=function(TheCtype, TheInfo)
  local ListIchange, ListKept, eTri, TheInt, NewFamily, NewVectors, ListGiHi, RemainingVects, ListIdxDiff, SingVect, AuthLength, n;
  ListIchange:=[];
  ListKept:=[];
  for eTri in TheInfo
  do
    Add(ListIchange, eTri[1]);
    Append(ListKept, eTri[2]);
  od;
  TheInt:=Intersection(Set(ListIchange), Set(ListKept));
  if Length(TheInt)<>0 then
    Print("We have a problem, please come back to drawing board");
    return fail;
  fi;
  NewVectors:=[];
  for eTri in TheInfo
  do
    Add(NewVectors, -TheCtype[eTri[2][1]]+TheCtype[eTri[2][2]]);
    Add(NewVectors, +TheCtype[eTri[2][1]]-TheCtype[eTri[2][2]]);
  od;
  NewVectors:=Set(NewVectors);
  if Length(NewVectors)<>2 then
    Print("The length should be exactly 2");
    return fail;
  fi;
  SingVect:=NewVectors[1];
  n:=Length(SingVect);
  ListIdxDiff:=Difference([1..Length(TheCtype)], Set(ListIchange));
  RemainingVects:=Set(TheCtype{ListIdxDiff});
  if Length(Intersection(RemainingVects, NewVectors)) <> 0 then
    Print("Intersection between the old vectors and the new ones");
    return fail;
  fi;
  NewFamily:=Concatenation(RemainingVects, NewVectors);
  AuthLength:=2*(2^n-1);
  if Length(NewFamily)<>AuthLength then
    Print("Wrong number of vectors");
    return fail;
  fi;
  return Set(NewFamily);
end;


CTYP_CharInvariantCtype:=function(TheCtype)
  local ScalarMat, DistMat;
  ScalarMat:=__VectorConfigurationFullDim_ScalarMat(TheCtype);
  DistMat:=MappedScalarMatrixDistanceMatrix(ScalarMat);
  return CanonicalStringEdgeColoredGraph(DistMat);
end;



LinearProgrammingElimination:=function(TheBasis, ListIneq, n)
  local ListPos, ListInequalitiesRed, ListInformationsRed;
#  ListInequalitiesRed:=EliminationByRedundancyDirectCDD(ListInequalities);
#  ListPos:=List(ListInequalitiesRed, x->Position(ListInequalities, x));
  ListPos:=RedundancyCheck(ListIneq.ListInequalities);
  ListInequalitiesRed:=ListIneq.ListInequalities{ListPos};
  ListInformationsRed:=ListIneq.ListInformations{ListPos};
  return rec(ListInequalities:=ListInequalitiesRed, ListInformations:=ListInformationsRed);
end;


RetrievingNonRedundantFacet:=function(FAC, GRPfac)
  local nbFac, Ofac, ListPos, BoundSet, TheDim;
  nbFac:=Length(FAC);
  Print(NullMat(5));
  Ofac:=Orbits(GRPfac, [1..nbFac], OnPoints);
  TheDim:=Length(FAC[1]);
  Print("RetrievingNonRedundantFacet nbFac=", nbFac, " |Ofac|=", Length(Ofac), " |GRPfac|=", Order(GRPfac), "\n");
  if Order(GRPfac)>0 then
#    BoundSet:=List(GetInitialRays_LinProg(FAC, TheDim), x->__FindFacetInequality(FAC, x));
    BoundSet:=[];
    ListPos:=EliminationByRedundancyEquivariant(FAC, BoundSet, GRPfac).eSetSelect;
    return ListPos;
  fi;
  # Doing a direct attack
  ListPos:=RedundancyCheck(FAC);
  return ListPos;
end;


# NOTE:
# direct dual description computation by cdd from the inequalities does
# not work. There are simply too many of them
CTYP_PolyhedralComputations:=function(TheBasis, RecIneq, n)
  local ThePointInterior, GramMat, i, GRPmatr, MapListInequality, GRPfac, ListPos, eInvariant, TheDim, ListGenFac, ListPosRed, GetPermGroupIneq, GRPfac2, TheCtypeCan, nbFail, TheFlip, eFacOrb;
  #
  # First computing an interior point. That is supposed to be cheap.
  #
  ThePointInterior:=GetSpaceInteriorPoint_NoGroup(RecIneq.ListInequalities);
  GramMat:=NullMat(n,n);
  TheDim:=Length(TheBasis);
  for i in [1..TheDim]
  do
    GramMat:=GramMat+ThePointInterior[i]*TheBasis[i];
  od;
  GRPmatr:=ArithmeticAutomorphismGroup([GramMat]);
  MapListInequality:=function(ListIneq, eGen)
    local TheBasisExpand, eGenSpace, NewList, eIneq, NewIneq, pos, ePerm;
    TheBasisExpand:=List(TheBasis, SymmetricMatrixToVector);
    eGenSpace:=List(TheBasis, x->SolutionMat(TheBasisExpand, SymmetricMatrixToVector(eGen*x*TransposedMat(eGen))));
    NewList:=[];
    for eIneq in ListIneq
    do
      NewIneq:=eIneq*CongrMap(eGenSpace);
      pos:=Position(ListIneq, NewIneq);
      if pos=fail then
        Error("We found pos=fail");
      fi;
      Add(NewList, pos);
    od;
    ePerm:=PermList(NewList);
    if ePerm=fail then
      Error("We found ePerm=fail");
    fi;
    return ePerm;
  end;
  GetPermGroupIneq:=function(ListIneq, eGRP)
    local ListGenFac;
    ListGenFac:=List(GeneratorsOfGroup(eGRP), eGen->MapListInequality(ListIneq, eGen));
    return Group(ListGenFac);
  end;
  GRPfac:=GetPermGroupIneq(RecIneq.ListInequalities, GRPmatr);
  Print("We have |GRPmatr|=", Order(GRPmatr), "  |GRPfac|=", Order(GRPfac), "\n");
  #
#  FAC:=RecIneq.ListInequalities;
#  RemoveFileIfExist("/tmp/Redund.fac");
#  output:=OutputTextFile("/tmp/Redund.fac", true);;
#  CPP_WriteMatrix(output, FAC);
#  CloseStream(output);
  #
  ListPos:=RetrievingNonRedundantFacet(RecIneq.ListInequalities, GRPfac);
  Print("|RecIneq.ListInequalities|=", Length(RecIneq.ListInequalities), " |ListPos|=", Length(ListPos), "\n");
  GRPfac2:=GetPermGroupIneq(RecIneq.ListInequalities{ListPos}, GRPmatr);
  ListPosRed:=List(Orbits(GRPfac2, [1..Length(ListPos)], OnPoints), x->ListPos[x[1]]);
  Print("|GRPfac2|=", Order(GRPfac2), " |ListPosRed|=", Length(ListPosRed), "\n");
  nbFail:=0;
  for eFacOrb in RecIneq.ListInformations
  do
    TheFlip:=CTYP_TheFlipping(RecIneq.TheCtype, eFacOrb);
    if TheFlip=fail then
      nbFail:=nbFail+1;
    fi;
  od;
  Print("nbFail=", nbFail, " |RecIneq.ListInformations|=", Length(RecIneq.ListInformations), "\n");
  return rec(TheCtype:=RecIneq.TheCtype,
             ListInequalities:=RecIneq.ListInequalities{ListPosRed},
             ListInformations:=RecIneq.ListInformations{ListPosRed},
             CharMat:=GramMat);
end;


CTYP_GetGramMatricesExtremeRays:=function(TheBasis, RecIneq, n)
  local ListPos, TheDim, ListIneqRed, EXT, ListGram, eEXT, GramMat, i, GramMatRed;
  ListPos:=RedundancyCheck(RecIneq.ListInequalities);
  TheDim:=Length(TheBasis);
  ListIneqRed:=List(RecIneq.ListInequalities{ListPos}, x->x{[2..TheDim+1]});
  EXT:=DualDescription(ListIneqRed);
  ListGram:=[];
  for eEXT in EXT
  do
    GramMat:=NullMat(n,n);
    for i in [1..TheDim]
    do
      GramMat:=GramMat+eEXT[i]*TheBasis[i];
    od;
    GramMatRed:=RemoveFractionMatrix(GramMat);
    Add(ListGram, GramMatRed);
  od;
  return rec(ListGram:=ListGram,
             FAC:=ListIneqRed,
             EXT:=EXT);
end;







CTYP_EnumerateCtypes:=function(n, ePrefix)
  local ListCtypeFull, FuncInsertCtype, IsFinished, nbOrbit, iOrb, ListFacets, eFac, TheFlip, eChar, RecIneq, eInsertable, TheBasis, DelCO, InitialCtype, TheGroup, iFacOrb, nbFacOrb, eFacOrb, FileName, eFullRecord;
  ListCtypeFull:=[];
  if ePrefix<>"unset" then
    iOrb:=0;
    while(true)
    do
      FileName:=Concatenation(ePrefix, "Ctyp", String(n), "_", String(iOrb+1));
      if IsExistingFile(FileName)=false then
        break;
      fi;
      Add(ListCtypeFull, ReadAsFunction(FileName)());
      iOrb:=iOrb+1;
    od;
  fi;
  TheBasis:=CTYP_GetBasis(n);
  FuncInsertCtype:=function(TheCtype)
    local TheCtypeCan, eCtypeFull, TheCtypeFull, FileName, test;
    TheCtypeCan:=LinPolytopeIntegral_CanonicalForm(TheCtype).EXT;
    for eCtypeFull in ListCtypeFull
    do
      if eCtypeFull.TheCtype = TheCtypeCan then
        return;
      fi;
    od;
    TheCtypeFull:=rec(TheCtype:=TheCtypeCan, Status:="NO");
    Add(ListCtypeFull, TheCtypeFull);
    if ePrefix<>"unset" then
      FileName:=Concatenation(ePrefix, "Ctyp", String(n), "_", String(Length(ListCtypeFull)));
      SaveDataToFile(FileName, TheCtypeFull);
    fi;
    Print("Now we have ", Length(ListCtypeFull), " Ctypes\n");
  end;
  if Length(ListCtypeFull)=0 then
    DelCO:=VOR_LTYPE_GetPrincipalType(n);
    TheGroup:=Group([-IdentityMat(n)]);
    InitialCtype:=CTYP_GetCtypeFromLtype(DelCO, TheGroup);
    FuncInsertCtype(InitialCtype);
  fi;
  while(true)
  do
    IsFinished:=true;
    nbOrbit:=Length(ListCtypeFull);
    for iOrb in [1..nbOrbit]
    do
      if ListCtypeFull[iOrb].Status="NO" then
        Print("Beginning treatment of orbit ", iOrb, "\n");
        IsFinished:=false;
        #
        RecIneq:=CTYP_GetInequalitiesOfCtype(ListCtypeFull[iOrb].TheCtype, TheBasis, n);
        eFullRecord:=CTYP_PolyhedralComputations(TheBasis, RecIneq, n);
        nbFacOrb:=Length(eFullRecord.ListInformations);
        for iFacOrb in [1..nbFacOrb]
        do
          Print("iOrb=", iOrb, "/", nbOrbit, "   iFacOrb=", iFacOrb, "/", nbFacOrb, " |ListCtypeFull|=", Length(ListCtypeFull), "\n");
          eFacOrb:=eFullRecord.ListInformations[iFacOrb];
          TheFlip:=CTYP_TheFlipping(eFullRecord.TheCtype, eFacOrb);
          FuncInsertCtype(TheFlip);
        od;
        ListCtypeFull[iOrb].Status:="YES";
        if ePrefix<>"unset" then
          FileName:=Concatenation(ePrefix, "Ctyp", String(n), "_", String(iOrb));
          SaveDataToFile(FileName, ListCtypeFull[iOrb]);
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return ListCtypeFull;
end;


CTYP_FullEnumerationOfComplex:=function(n, ListTotal)
  local TotDim, TheBasis, ListEXT, eCone, RecIneq, ListGram, List_ListEXT, iDim, eDim, ListRec, FuncInsert, fEntry, ListSets, eSet, ListGramSel, SumGram, eInv, eRec, iCone, nbCone, ListVect, EulerPoincare, SumInvStab, GRP, eEntry;
  TotDim:=n*(n+1)/2;
  TheBasis:=CTYP_GetBasis(n);
  ListEXT:=[];
  nbCone:=Length(ListTotal);
  for iCone in [1..nbCone]
  do
    eCone:=ListTotal[iCone];
    Print("iCone=", iCone, " / ", nbCone, "\n");
    RecIneq:=CTYP_GetInequalitiesOfCtype(eCone.TheCtype, TheBasis, n);
    ListGram:=CTYP_GetGramMatricesExtremeRays(TheBasis, RecIneq, n).ListGram;
    Print("  |ListInequalities|=", Length(RecIneq.ListInequalities), "  |ListInformations|=", Length(RecIneq.ListInformations), "  |ListGram|=", Length(ListGram), "\n");
    Add(ListEXT, ListGram);
  od;
  List_ListEXT:=[ListEXT];
  for iDim in [1..TotDim-1]
  do
    eDim:=TotDim - iDim;
    ListRec:=[];
    FuncInsert:=function(eRec)
      local fRec, test;
      for fRec in ListRec
      do
        if fRec.eInv=eRec.eInv then
          test:=ArithmeticIsomorphism([eRec.SumGram], [fRec.SumGram]);
          if test<>false then
            return;
          fi;
        fi;
      od;
      Add(ListRec, eRec);
    end;
    for fEntry in List_ListEXT[iDim]
    do
      ListVect:=List(fEntry, SymmetricMatrixToVector);
      ListSets:=DualDescriptionSets(ListVect);
      for eSet in ListSets
      do
        ListGramSel:=fEntry{eSet};
        SumGram:=Sum(ListGramSel);
        if IsPositiveDefiniteSymmetricMatrix(SumGram) then
          eInv:=GetInvariantGram(SumGram);
          eRec:=rec(ListGram:=ListGramSel, SumGram:=SumGram, eInv:=eInv);
          FuncInsert(eRec);
        fi;
      od;
    od;
    Add(List_ListEXT, List(ListRec, x->x.ListGram));
    Print("iDim=", iDim, " |ListEXT|=", Length(ListRec), "\n");
  od;
  #
  # Euler Poincare Characteristic
  #
  EulerPoincare:=0;
  for iDim in [1..TotDim]
  do
    SumInvStab:=0;
    for eEntry in List_ListEXT[iDim]
    do
      SumGram:=Sum(eEntry);
      GRP:=ArithmeticAutomorphismGroup([SumGram]);
      SumInvStab:=SumInvStab + 1/Order(GRP);
    od;
    EulerPoincare:=EulerPoincare + (-1)^(iDim) * SumInvStab;
  od;
  Print("EulerPoincare=", EulerPoincare, "\n");
  return List_ListEXT;
end;


CTYP_GetParityClasses:=function(n)
  return Filtered(BuildSet(n, [0,1/2]), x->Sum(x)>0);
end;


CTYP_SpanCone:=function(TheCtype, TheBasis, n)
  local ListParity, ListResidue, ListCharVect, RecIneq, ListGram, ListVect, eGram, eVect;
  ListParity:=CTYP_GetParityClasses(n);
  ListResidue:=List(TheCtype, x->(x mod 2)/2);
  ListCharVect:=List(ListParity, x->TheCtype[Position(ListResidue, x)]);
  RecIneq:=CTYP_GetInequalitiesOfCtype(TheCtype, TheBasis, n);
  ListGram:=CTYP_GetGramMatricesExtremeRays(TheBasis, RecIneq, n).ListGram;
  #
  ListVect:=[];
  for eGram in ListGram
  do
    eVect:=List(ListCharVect, x->x*eGram*x);
    Add(ListVect, eVect);
  od;
  return ListVect;
end;

CTYP_ComputingThetaMaps:=function(TheCtype, TheBasis, n)
  local eVectZero, ListClasses, CtypeExpanded, ListResidue, ListCharVect, RecIneq, ListGram, nbClass, TheMatrix, iClass, jClass, eProd, ListThetaMap, eGram, eVect, eThetaMap, eV, IsZonotopal, FACredNN, LinSpa, FullFAC, EXTray_LinSpa, EXTray_Basis, EXTray_SymMat, Basis_ThetaMap, RecFAC_EXT, eCharVect, ListVal, eVal, FACred, eBasMat;
  eVectZero:=ListWithIdenticalEntries(n, 0);
  ListClasses:=BuildSet(n, [0,1/2]);
  CtypeExpanded:=Concatenation([eVectZero], TheCtype);
  ListResidue:=List(CtypeExpanded, x->(x mod 2)/2);
  ListCharVect:=List(ListClasses, x->CtypeExpanded[Position(ListResidue, x)]);
  RecIneq:=CTYP_GetInequalitiesOfCtype(TheCtype, TheBasis, n);
  RecFAC_EXT:=CTYP_GetGramMatricesExtremeRays(TheBasis, RecIneq, n);
  #
  nbClass:=Length(ListClasses);
  TheMatrix:=NullMat(nbClass, nbClass);
  for iClass in [1..nbClass]
  do
    for jClass in [1..nbClass]
    do
      eProd:=4 * ListClasses[iClass] * ListClasses[jClass];
      TheMatrix[iClass][jClass]:=(-1)^(eProd);
    od;
  od;
  #
  ListThetaMap:=[];
  for eGram in RecFAC_EXT.ListGram
  do
    eVect:=[];
    for iClass in [1..nbClass]
    do
      eCharVect:=ListCharVect[iClass];
      eV:=eCharVect;
      eVal:= - eV * eGram * eV;
      Add(eVect, eVal);
    od;
    eThetaMap:=eVect*TheMatrix;
    Add(ListThetaMap, eThetaMap);
  od;
  #
  # Building the set of inequalities
  #
  Basis_ThetaMap:=[];
  for eBasMat in TheBasis
  do
    eVect:=List(ListCharVect, x-> - x*eBasMat*x);
    eThetaMap:=eVect*TheMatrix;
    Add(Basis_ThetaMap, eThetaMap);
  od;
  FullFAC:=[];
  for iClass in [2..nbClass]
  do
    ListVal:=List(Basis_ThetaMap, x->x[iClass]);
    Add(FullFAC, ListVal);
  od;
  Append(FullFAC, RecFAC_EXT.FAC);
  #
  # Construction of the nonnegativity cone:
  # The matrices A such that Theta_v(A) >= 0 for v<>0
  # Conjecture is that those are all the zonotopal.
  #
  LinSpa:=LinearDeterminedByInequalities(FullFAC);
  FACred:=List(FullFAC, x->x*TransposedMat(LinSpa));
  FACredNN:=Filtered(FACred, x->x*x<>0);
  EXTray_LinSpa:=DualDescription(FACredNN);
  EXTray_Basis:=List(EXTray_LinSpa, x->x*LinSpa);
  EXTray_SymMat:=List(EXTray_Basis, x->x*TheBasis);
  #
  IsZonotopal:=First(EXTray_SymMat, x->IsRankOneMatrix(x).result=false)=fail;
  return rec(ListThetaMap:=ListThetaMap, IsZonotopal:=IsZonotopal, EXTray_SymMat:=EXTray_SymMat);
end;

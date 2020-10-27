VOR_L1_ComputeNorm:=function(eRecL1, eVect)
  return Maximum(List(eRecL1.MatrixVector, x->x*eVect));
end;


VOR_L1_GetNumberCheck:=function()
  return 0;
end;


VOR_L1_ComputeNorm_Attain:=function(eRecL1, eVect)
  local MatrixVector, ListScal, eMax, eSet;
  MatrixVector:=eRecL1.MatrixVector;
  ListScal:=List(MatrixVector, x->x*eVect);
  eMax:=Maximum(ListScal);
  eSet:=Filtered([1..Length(ListScal)], x->ListScal[x]=eMax);
  return rec(eNorm:=eMax, ListAtt:=eSet);
end;


VOR_L1_GetHyperplanes:=function(eRecL1)
  local ListDiff, ePair, eDiff, eDiffRed, fPair, eSet1;
  ListDiff:=[];
  for ePair in Combinations(eRecL1.MatrixVector, 2)
  do
    eDiff:=ePair[1] - ePair[2];
    eDiffRed:=RemoveFraction(eDiff);
    fPair:=Set([eDiffRed, eDiffRed]);
    Add(ListDiff, fPair);
  od;
  eSet1:=Set(List(Set(ListDiff), x->x[1]));
  return Difference(eSet1, Set(eRecL1.MatrixVector));
end;



VOR_L1_TestCorrectnessRecL1:=function(eRecL1)
  local FAC, eVect, eIneq, FACirred, eGen, eList;
  FAC:=[];
  for eVect in eRecL1.MatrixVector
  do
    eIneq:=Concatenation([1], eVect);
    Add(FAC, RemoveFraction(eIneq));
  od;
  FACirred:=RemoveRedundancyByDualDescription(FAC);
  if Length(FACirred)<>Length(FAC) then
    Error("FACirred different from FAC");
  fi;
  for eGen in GeneratorsOfGroup(eRecL1.PointGRP)
  do
    eList:=List(eRecL1.MatrixVector, x->Position(eRecL1.MatrixVector, x*TransposedMat(eGen)));
    if PermList(eList)=fail then
      Error("Error in the generator");
    fi;
  od;
  return true;
end;



VOR_L1_FindShortVectors:=function(eRecL1, eNorm)
  local FAC, eLine, nLine, TheResult;
  FAC:=[];
  for eLine in eRecL1.MatrixVector
  do
    nLine:=Concatenation([eNorm], -eLine);
    Add(FAC, nLine);
  od;
  TheResult:=RunZsolve(FAC);
#  Print("TheResult=", TheResult, "\n");
  return TheResult.TheINH;
end;

VOR_L1_FindInvariantBasis:=function(eRecL1)
  local n, eNorm, ListVect, ListNorm, SetNorm, hNorm, eSet, ListVectSel, eDet;
  eNorm:=1;
  n:=eRecL1.n;
  while(true)
  do
    ListVect:=VOR_L1_FindShortVectors(eRecL1, eNorm);
#    Print("ListVect=", ListVect, "\n");
    ListNorm:=List(ListVect, x->VOR_L1_ComputeNorm(eRecL1, x));
    SetNorm:=Set(ListNorm);
    for hNorm in SetNorm
    do
      eSet:=Filtered([1..Length(ListNorm)], x->ListNorm[x]<=hNorm);
      ListVectSel:=ListVect{eSet};
      if RankMat(ListVectSel)=n then
        eDet:=AbsInt(DeterminantMat(BaseIntMat(ListVectSel)));
        if eDet=1 then
          return ListVectSel;
        fi;
      fi;
    od;
    eNorm:=eNorm+1;
  od;
end;

VOR_Linfinity_Rectangle_eRecL1:=function(a)
  local MatrixVector, n, eMat1, eMat2, eMat3, PointGRP, eRecL1, eInvBasis;
  MatrixVector:=[[1,0],[-1,0],    [0,a], [0,-a]];
  n:=2;
  eMat1:=[[-1,0], [0, 1]];
  eMat2:=[[1, 0], [0,-1]];
  eMat3:=[[0,1], [1,0]];
  if a=1 then
    PointGRP:=Group([eMat1, eMat2, eMat3]);
  else
    PointGRP:=Group([eMat1, eMat2]);
  fi;
  eRecL1:=rec(n:=n,
             PointGRP:=PointGRP,
             MatrixVector:=MatrixVector);
#  Print("Before eInvBasis computation\n");
  eInvBasis:=VOR_L1_FindInvariantBasis(eRecL1);
#  Print("We have eInvBasis\n");
  eRecL1.eInvBasis:=eInvBasis;
  return eRecL1;
end;



Vor_Linfinity_L1_An:=function(n)
  local ListVect, i, eVect, GramMat, GRPmatr, LMat_Li, LMat_L1, GetRec, GRPaff, ListGensAff;
  ListVect:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n+1,0);
    eVect[i]:=1;
    eVect[i+1]:=-1;
    Add(ListVect, eVect);
  od;
  GramMat:=ListVect*TransposedMat(ListVect);
  GRPmatr:=ArithmeticAutomorphismGroup([GramMat]);
  ListGensAff:=List(GeneratorsOfGroup(GRPmatr), x->FuncCreateBigMatrix(ListWithIdenticalEntries(n,0), x));
  GRPaff:=Group(ListGensAff);
  LMat_Li:=Concatenation(IdentityMat(n+1), -IdentityMat(n+1));
  LMat_L1:=BuildSet(n+1, [-1,1]);
  GetRec:=function(LMat)
    local MatrixVector, eVmat, Lscal, eRecL1, eInvBasis;
    MatrixVector:=[];
    for eVmat in LMat
    do
      Lscal:=List(ListVect, x->x*eVmat);
      Add(MatrixVector, Lscal);
    od;
    eRecL1:=rec(n:=n,
                GramMat:=GramMat, 
                PointGRP:=GRPmatr, 
                GRPaff:=GRPaff, 
                ListVect:=ListVect, 
                MatrixVector:=MatrixVector);
    eInvBasis:=VOR_L1_FindInvariantBasis(eRecL1);
    eRecL1.eInvBasis:=eInvBasis;
    return eRecL1;
  end;
  return rec(eRec_L1:=GetRec(LMat_L1),
             eRec_Li:=GetRec(LMat_Li));
end;



Vor_Linfinity_L1_Dn:=function(n)
  local ListVect, i, eVect, GramMat, GRPmatr, LMat_Li, LMat_L1, GetRec, eRecLattD, ListMatrGens, ListMatrGensB, eGen, j, eMatr;
  eRecLattD:=LatticeDn(n);
  ListVect:=eRecLattD.TheBasis;
  GramMat:=ListVect*TransposedMat(ListVect);
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(SymmetricGroup(n))
  do
    eMatr:=NullMat(n,n);
    for i in [1..n]
    do
      j:=OnPoints(i, eGen);
      eMatr[i][j]:=1;
    od;
    Add(ListMatrGens, eMatr);
  od;
  eMatr:=NullMat(n,n);
  eMatr[1][1]:=-1;
  for i in [2..n]
  do
    eMatr[i][i]:=1;
  od;
  Add(ListMatrGens, eMatr);
  ListMatrGensB:=List(ListMatrGens, x->ListVect*x*Inverse(ListVect));
  if First(ListMatrGensB, x->x*GramMat*TransposedMat(x)<>GramMat)<>fail then
    Error("Error in our construction of restricted group\n");
  fi;
  GRPmatr:=Group(ListMatrGensB);
#  GRPmatr:=ArithmeticAutomorphismGroup([GramMat]);
  LMat_Li:=Concatenation(IdentityMat(n), -IdentityMat(n));
  LMat_L1:=BuildSet(n, [-1,1]);
  GetRec:=function(LMat)
    local MatrixVector, eVmat, Lscal, eRecL1, eInvBasis;
    MatrixVector:=[];
    for eVmat in LMat
    do
      Lscal:=List(ListVect, x->x*eVmat);
      Add(MatrixVector, Lscal);
    od;
    eRecL1:=rec(n:=n,
                GramMat:=GramMat, 
                PointGRP:=GRPmatr, 
                ListVect:=ListVect, 
                MatrixVector:=MatrixVector);
    eInvBasis:=VOR_L1_FindInvariantBasis(eRecL1);
    eRecL1.eInvBasis:=eInvBasis;
    return eRecL1;
  end;
  return rec(eRec_L1:=GetRec(LMat_L1),
             eRec_Li:=GetRec(LMat_Li));
end;





VOR_L1_FindClose:=function(eRecL1, eVect, eNorm)
  local FAC, eLine, eScal, nLine, TheResult;
  FAC:=[];
  for eLine in eRecL1.MatrixVector
  do
    eScal:=eVect*eLine;
    nLine:=Concatenation([eNorm-eScal], -eLine);
    Add(FAC, nLine);
  od;
  TheResult:=RunZsolve(FAC);
  return TheResult.TheINH;
end;



VOR_L1_FindClosest:=function(eRecL1, eVect)
  local n, StartVect, TheGraverBasis, eNorm, IsFinished, eGraver, NewVect, NewNorm, FAC, eLine, eScal, nLine, TheResult, TheListCand, ListNorm, MinNorm, eCand, MatrixVector;
  n:=eRecL1.n;
  StartVect:=ListWithIdenticalEntries(n,0);
  MatrixVector:=eRecL1.MatrixVector;
  TheGraverBasis:=Concatenation(IdentityMat(n), -IdentityMat(n));
  eNorm:=VOR_L1_ComputeNorm(eRecL1, eVect);
  while(true)
  do
    IsFinished:=true;
    for eGraver in TheGraverBasis
    do
      NewVect:=StartVect + eGraver;
      NewNorm:=VOR_L1_ComputeNorm(eRecL1, eVect - NewVect);
      if NewNorm < eNorm then
        IsFinished:=false;
        eNorm:=NewNorm;
        StartVect:=NewVect;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  #
  FAC:=[];
  for eLine in MatrixVector
  do
    eScal:=eVect*eLine;
    nLine:=Concatenation([eNorm+eScal], -eLine);
    Add(FAC, RemoveFraction(nLine));
  od;
  TheResult:=RunZsolve(FAC);
  TheListCand:=TheResult.TheINH;
  if Length(TheListCand)=0 then
    Error("TheListCand must be non-empty, since we have one element");
  fi;
  ListNorm:=List(TheListCand, x->VOR_L1_ComputeNorm(eRecL1, eVect - x));
  MinNorm:=Minimum(ListNorm);
  eCand:=Filtered([1..Length(ListNorm)], x->ListNorm[x]=MinNorm);
  return TheListCand{eCand};
end;






VOR_L1_FindShortestVectors:=function(eRecL1)
  local n, TheGraverBasis, MatrixVector, i, StartVect, eNorm, IsFinished, eGraver, NewVect, NewNorm, ListVectRet, eSet, GuessMinimumVect, GuessMinimumNorm, ListVect, ListNorm, MinNorm;
  n:=eRecL1.n;
  TheGraverBasis:=Concatenation(IdentityMat(n), -IdentityMat(n));
  MatrixVector:=eRecL1.MatrixVector;
  for i in [1..n]
  do
    StartVect:=ListWithIdenticalEntries(n,0);
    StartVect[i]:=1;
    eNorm:=VOR_L1_ComputeNorm(eRecL1, StartVect);
    while(true)
    do
      IsFinished:=true;
      for eGraver in TheGraverBasis
      do
        NewVect:=StartVect + eGraver;
        if NewVect<>ListWithIdenticalEntries(n,0) then
          NewNorm:=VOR_L1_ComputeNorm(eRecL1, StartVect);
          if NewNorm < eNorm then
            IsFinished:=false;
            eNorm:=NewNorm;
            StartVect:=NewVect;
          fi;
        fi;
      od;
      if IsFinished then
        break;
      fi;
    od;
    if i=1 then
      GuessMinimumVect:=StartVect;
      GuessMinimumNorm:=eNorm;
    else
      if eNorm<GuessMinimumNorm then
        GuessMinimumVect:=StartVect;
        GuessMinimumNorm:=eNorm;
      fi;
    fi;
  od;
  #
  # Now using RunZSolve for finding absolute minimum
  #
  ListVect:=VOR_L1_FindShortVectors(eRecL1, eNorm);
  ListNorm:=List(ListVect, x->VOR_L1_ComputeNorm(eRecL1, x));
  SetNorm:=Set(ListNorm);
  MinNorm:=Minimum(Difference(SetNorm, [0]));
  eSet:=Filtered([1..Length(ListNorm)], x->ListNorm[x]=MinNorm);
  ListVectRet:=ListVect{eSet};
  return ListVectRet;
end;


VOR_L1_GetReductionIndex:=function(ListListVect)
  local n, nbFam, iFam, ListVect, jFam;
  n:=Length(ListListVect[1][1]);
  nbFam:=Length(ListListVect);
  for iFam in [1..nbFam]
  do
    ListVect:=[];
    for jFam in [1..iFam]
    do
      Append(ListVect, ListListVect[jFam]);
    od;
    if RankMat(ListVect)=n then
      return iFam;
    fi;
  od;
end;

# We do not use Homogeneous coordinates.
# So all polytope computations need to add it.
# 
# eRecCompFacet is a component of the Voronoi
# complex (not necessarily a polytope) associated to
# the polyhedral metric.
# rec(SinglePt:=....
#     LinSpace:=.....
#     ListEqui:=[fRec1, fRec2, ....], 
#     ListRelevant:=[eRec1, eRec2, .....])
# With eRec1, eRec2, .... being of the form
# rec(ePt:=.....  , posIneq:=idx)
#
# The inequalities are for each point
# fIneq.(a +b*x - v) <= eIneq.(a + b*x - v)
# 0 <= (eIneq - fIneq).(b*x + a-v )
# That is the fIneq is dominated by all eIneq
#
# But we have also the inequalities of shortest vectors
# eIneq.(a + b*x - v) >= eEqui.(a + b*x - w)
# [eIneq.(a-v) - eEqui.(a - w) ] + (eIneq - eEqui).(b*x) >= 0
# 
# a set eRecCompFacet is called valid if
# for all points v s.t. v attains the minimum on eRecCompFacet,
# the inequality l1(x-v) >= l2(x-v) is valid.
VOR_L1_GetInequalities:=function(eRecL1, eRecCompFacet)
  local ListIneqRed, ListIneqType, nbIneq, n, eEqui, eRelevant, iIneq, eIneq, jIneq, fIneq, eDiff, eScal, Lscal, eFAC, eType, iIneqEqui, fIneqEqui, nbRelevant, iRelevant;
  ListIneqRed:=[];
  ListIneqType:=[];
  nbIneq:=Length(eRecL1.MatrixVector);
  n:=eRecL1.n;
  eEqui:=eRecCompFacet.ListEqui[1];
  nbRelevant:=Length(eRecCompFacet.ListRelevant);
  for iRelevant in [1..nbRelevant]
  do
    eRelevant:=eRecCompFacet.ListRelevant[iRelevant];
    iIneq:=eRelevant.posIneq;
    eIneq:=eRecL1.MatrixVector[iIneq];
    for jIneq in Difference([1..nbIneq], [iIneq])
    do
      fIneq:=eRecL1.MatrixVector[jIneq];
      eDiff:=eIneq - fIneq;
      eScal:=eDiff * (eRecCompFacet.SinglePt - eRelevant.ePt);
      Lscal:=List(eRecCompFacet.LinSpace, x->eDiff*x);
      eFAC:=Concatenation([eScal], Lscal);
      eType:=rec(type:="dom norm", iIneq:=iIneq, jIneq:=jIneq, iRelevant:=iRelevant);
      Add(ListIneqRed, eFAC);
      Add(ListIneqType, eType);
    od;
    #
    iIneqEqui:=eEqui.posIneq;
    fIneqEqui:=eRecL1.MatrixVector[iIneqEqui];
    eDiff:=eIneq - fIneqEqui;
    eScal:=eIneq*(eRecCompFacet.SinglePt - eRelevant.ePt) - fIneqEqui*(eRecCompFacet.SinglePt - eEqui.ePt);
    Lscal:=List(eRecCompFacet.LinSpace, x->eDiff*x);
    eFAC:=Concatenation([eScal], Lscal);
    eType:=rec(type:="nearest", iRelevant:=iRelevant);
    Add(ListIneqRed, eFAC);
    Add(ListIneqType, eType);
  od;
  return rec(ListIneqRed:=ListIneqRed, ListIneqType:=ListIneqType);
end;

VOR_L1_GetVertices:=function(eRecL1, eRecCompFacet)
  local eRecIneq, EXTred, RelDim, EXT, eEXT, eEXTred, ePt, i, PreEXTred, EXText;
  if IsBound(eRecCompFacet.ListIneqIrred) then
    PreEXTred:=DualDescription(eRecCompFacet.ListIneqIrred);
  else
    eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
    Print("VOR_L1_GetVertices |ListIneqRed|=", Length(eRecIneq.ListIneqRed), "\n");
    PreEXTred:=DualDescription(eRecIneq.ListIneqRed);
  fi;
  RelDim:=Length(eRecCompFacet.LinSpace);
  EXT:=[];
  EXTred:=[];
  for eEXT in PreEXTred
  do
    eEXTred:=eEXT{[2..RelDim+1]}/eEXT[1];
    Add(EXTred, eEXT/eEXT[1]);
    ePt:=eRecCompFacet.SinglePt;
    for i in [1..RelDim]
    do
      ePt:=ePt + eEXTred[i]*eRecCompFacet.LinSpace[i];
    od;
    Add(EXT, ePt);
  od;
  EXText:=List(EXT, x->Concatenation([1], x));
  return rec(EXT:=EXT, EXText:=EXText, EXTred:=EXTred);
end;


VOR_L1_GetFacetMidElement:=function(eRecL1, eRecCompFacet)
  local eRecIneq, ListIneqCan, RelDim, nbIneq, SetIneqCan, EXT, nbIneqCan, ListIneqRed, ListListType, ListFacetPt, eIneqCan, EXTincd, rnk, eIso, ListMatch, eListType, ListFacetPtRed, eIsoRed, ePtFull, i;
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
  ListIneqCan:=List(eRecIneq.ListIneqRed, RemoveFraction);
  RelDim:=Length(ListIneqCan[1]);
  nbIneq:=Length(ListIneqCan);
  SetIneqCan:=Set(ListIneqCan);
  EXT:=DualDescription(SetIneqCan);
  nbIneqCan:=Length(SetIneqCan);
  ListIneqRed:=[];
  ListListType:=[];
  ListFacetPtRed:=[];
  ListFacetPt:=[];
  for eIneqCan in SetIneqCan
  do
    EXTincd:=Filtered(EXT, x->x*eIneqCan=0);
    rnk:=RankMat(EXTincd);
    if rnk=RelDim then
      Error("Inconsistency in the rank");
    fi;
    if rnk=RelDim-1 then
      eIso:=Isobarycenter(EXTincd);
      ListMatch:=Filtered([1..nbIneq], x->ListIneqCan[x]=eIneqCan);
      eListType:=eRecIneq.ListIneqType{ListMatch};
      eIsoRed:=eIso{[2..RelDim]};
      ePtFull:=eRecCompFacet.SinglePt;
      for i in [1..RelDim-1]
      do
        ePtFull:=ePtFull + eIsoRed[i]*eRecCompFacet.LinSpace[i];
      od;
      Add(ListIneqRed, eIneqCan);
      Add(ListListType, eListType);
      Add(ListFacetPtRed, eIso);
      Add(ListFacetPt, ePtFull);
    fi;
  od;
  return rec(ListIneqRed:=ListIneqRed,
             ListListType:=ListListType,
             ListFacetPtRed:=ListFacetPtRed, 
             ListFacetPt:=ListFacetPt);
end;


VOR_L1_RemoveRedundantPoints:=function(eRecL1, eRecCompFacet)
  local eRecInfo, nbClos, ListStatusClos, nbFacet, iFacet, eListType, eType, eSet;
  eRecInfo:=VOR_L1_GetFacetMidElement(eRecL1, eRecCompFacet);
  nbClos:=Length(eRecCompFacet.ListRelevant);
  ListStatusClos:=ListWithIdenticalEntries(nbClos,0);
  nbFacet:=Length(eRecInfo.ListIneqRed);
  for iFacet in [1..nbFacet]
  do
    eListType:=eRecInfo.ListListType[iFacet];
    for eType in eListType
    do
      if eType.type="nearest" then
        ListStatusClos[eType.iRelevant]:=1;
      fi;
    od;
  od;
  eSet:=Filtered([1..nbClos], x->ListStatusClos[x]=1);
  return rec(SinglePt:=eRecCompFacet.SinglePt, 
             LinSpace:=eRecCompFacet.LinSpace, 
             ListEqui:=eRecCompFacet.ListEqui, 
             ListRelevant:=eRecCompFacet.ListRelevant{eSet});
end;




VOR_L1_IsPointInside:=function(eRecL1, eRecCompFacet, ePt)
  local nbIneq, ePtEqui, eDist, eRec, eDiff, eNorm, eScal;
  nbIneq:=Length(eRecL1.MatrixVector);
  ePtEqui:=eRecCompFacet.ListEqui[1].ePt;
  eDist:=VOR_L1_ComputeNorm(eRecL1, ePtEqui - ePt);
  for eRec in eRecCompFacet.ListRelevant
  do
    eDiff:=eRec.ePt - ePt;
    eNorm:=VOR_L1_ComputeNorm(eRecL1, eDiff);
    if eNorm < eDist then
      return false;
    fi;
    eScal:=eDiff*eRecL1.MatrixVector[eRec.posIneq];
    if eScal < eNorm then
      return false;
    fi;
  od;
  return true;
end;


VOR_L1_TestEquivalenceVertices:=function(eRecL1, eVect1, eVect2)
  local eVectRed1, eVectRed2, eElt, eImg, eImgRed, eTrans, eBigMat;
  eVectRed1:=VectorMod1(eVect1);
  eVectRed2:=VectorMod1(eVect2);
  for eElt in eRecL1.PointGRP
  do
    eImg:=eVect1*eElt;
    eImgRed:=VectorMod1(eImg);
    if eImgRed=eVectRed2 then
      eTrans:=eVect2 - eVect1*eElt;
      eBigMat:=FuncCreateBigMatrix(eTrans, eElt);
      return rec(eTrans:=eTrans, eElt:=eElt, eBigMat:=eBigMat);
    fi;
  od;
  return false;
end;



VOR_L1_TestEquivalenceCompFacet:=function(eRecL1, eRecCompFacet1, eRecCompFacet2)
  local EXT1, EXT2, eIso1, eIso2, eIsoRed1, eIsoRed2, eElt, eImg, eImgRed, eTrans;
  EXT1:=VOR_L1_GetVertices(eRecL1, eRecCompFacet1).EXT;
  EXT2:=VOR_L1_GetVertices(eRecL1, eRecCompFacet2).EXT;
  eIso1:=Isobarycenter(EXT1);
  eIso2:=Isobarycenter(EXT2);
  return VOR_L1_TestEquivalenceVertices(eRecL1, eIso1, eIso2);
end;

VOR_L1_AutomorphismPoint:=function(eRecL1, ePoint)
  local n, ePointRed, ePointExp, ListMatrGens, ListAffGens, FuncInsertGen, GRPmatr, GRPaff, eElt, eImg;
  n:=eRecL1.n;
  ePointRed:=VectorMod1(ePoint);
  ePointExp:=Concatenation([1], ePoint);
  ListMatrGens:=[];
  ListAffGens:=[];
  GRPmatr:=Group([IdentityMat(n)]);
  GRPaff :=Group([IdentityMat(n+1)]);
  FuncInsertGen:=function(eElt)
    local eDiff, eBigMat;
    if eElt in GRPmatr then
      return;
    fi;
    Add(ListMatrGens, eElt);
    GRPmatr:=Group(ListMatrGens);
    eDiff:=ePoint - ePoint*eElt;
    eBigMat:=FuncCreateBigMatrix(eDiff, eElt);
    if ePointExp*eBigMat<>ePointExp then
      Error("Error in eIsoExp");
    fi;
    Add(ListAffGens, eBigMat);
    GRPaff:=Group(ListAffGens);
  end;
  for eElt in eRecL1.PointGRP
  do
    eImg:=ePoint*eElt;
    if VectorMod1(eImg)=ePointRed then
      FuncInsertGen(eElt);
    fi;
  od;
  return rec(GRPmatr:=GRPmatr, GRPaff:=GRPaff);
end;


VOR_L1_AutomorphismCompFacet:=function(eRecL1, eRecCompFacet)
  local n, eRecEXT, EXT, EXText, eIso, eRecGRP, ListPermGensEXT, eBigMat, eList, GRPext;
  n:=eRecL1.n;
  eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompFacet);
  EXT:=eRecEXT.EXT;
  EXText:=List(EXT, x->Concatenation([1], x));
  eIso:=Isobarycenter(EXT);
  eRecGRP:=VOR_L1_AutomorphismPoint(eRecL1, eIso);
  ListPermGensEXT:=[];
  for eBigMat in GeneratorsOfGroup(eRecGRP.GRPaff)
  do
    eList:=List(EXText, x->Position(EXText, x*eBigMat));
    Add(ListPermGensEXT, PermList(eList));
  od;
  GRPext:=Group(ListPermGensEXT);
  return rec(GRPmatr:=eRecGRP.GRPmatr,
             GRPaff:=eRecGRP.GRPaff,
             GRPext:=GRPext,
             EXT:=EXT,
             EXText:=EXText,
             EXTred:=eRecEXT.EXTred);
end;


# 
# We must have for all v defining the norm (MatrixVector)
# v.(x - ePt) <= vEqui.(x - ePtEqui)
# So, rewritten
# 0 <= -vEqui.ePtEqui + v.ePt + x.(vEqui - v)
# x is of the form a + b*y so this gives us
# 0 >= -vEqui.ePtEqui + v.ePt + (vEqui - v)*a +  (vEqui - v).b*x
VOR_L1_ComputeIntersection:=function(eRecL1, eRecCompFacet, ePt)
  local eRecIneq, eRecEqui, ePtEqui, eVectEqui, FACplus, eVect, vectDiff, Lscal, eVal, eFac, FACtot, TheSpann, ListIneq, EXTh, eEXT, eEXTn, hVal, EXT, TheDim, eEXT1, eEXT2, eEXT3, eEXT4;
  TheDim:=Length(eRecCompFacet.LinSpace);
  eRecEqui:=eRecCompFacet.ListEqui[1];
  ePtEqui:=eRecEqui.ePt;
  eVectEqui:=eRecL1.MatrixVector[eRecEqui.posIneq];
  FACplus:=[];
  for eVect in eRecL1.MatrixVector
  do
    hVal:=-eVectEqui*ePtEqui + eVect*ePt;
    vectDiff:=eVectEqui - eVect;
    Lscal:=List(eRecCompFacet.LinSpace, x->x*vectDiff);
    eVal:=hVal + vectDiff*eRecCompFacet.SinglePt;
    eFac:=Concatenation([eVal], Lscal);
    Add(FACplus, eFac);
  od;
  #
  FACtot:=Concatenation(eRecCompFacet.ListIneqIrred, FACplus);
  TheSpann:=LinearDeterminedByInequalities(FACtot);
#  Print("TheSpann=", TheSpann, "\n");
  if Length(TheSpann)=0 then
    return rec(Answer:="NoIntersection");
  fi;
  ListIneq:=List(FACtot, x->List(TheSpann, y->y*x));
  EXTh:=DualDescription(ListIneq);
  EXT:=[];
  for eEXT1 in EXTh
  do
    eEXT2:=eEXT1*TheSpann;
    eEXT3:=eEXT2{[2..TheDim+1]}/eEXT2[1];
    eEXT4:=eRecCompFacet.SinglePt + eEXT3*eRecCompFacet.LinSpace;
    Add(EXT, eEXT4);
  od;
  return rec(Answer:="intersect", EXT:=EXT);
end;


#
# The norm on the space is 
# We must have v.(x - h) <= vEqui.(x - PtEqui)
# for all v in MatrixVector
# for some x in the face
# Rewriting we get
# (v - vEqui).x + vEqui.PtEqui <= v.h
# or
# 0 <= -vEqui.PtEqui + (vEqui - v).x    +    v.h
# So we must take the minimum of (v-vEqui).x
# with x varying over the cell (vertices give that).
VOR_L1_GetFACnearest:=function(eRecL1, eRecCompFacet)
  local eRecEXT, eRecEqui, ePtEqui, eVectEqui, FAC, eVEct, Lscal, eVal, eFac, TheResult, eVect, ListPointEqui;
  eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompFacet);
  Print("|eRecEXT.EXT|=", Length(eRecEXT.EXT), "\n");
  eRecEqui:=eRecCompFacet.ListEqui[1];
  ePtEqui:=eRecEqui.ePt;
  eVectEqui:=eRecL1.MatrixVector[eRecEqui.posIneq];
  FAC:=[];
  for eVect in eRecL1.MatrixVector
  do
    Lscal:=List(eRecEXT.EXT, x->(eVect - eVectEqui)*x);
    eVal:=Minimum(Lscal) + ePtEqui*eVectEqui;
    eFac:=Concatenation([-eVal], eVect);
    Add(FAC, eFac);
  od;
  return FAC;
end;

VOR_L1_GetCandidateNearest:=function(eRecL1, eRecCompFacet)
  local FAC, FACirred, TheResult;
  FAC:=VOR_L1_GetFACnearest(eRecL1, eRecCompFacet);
  FACirred:=RemoveRedundancyByDualDescription(FAC);
#  Print("|FAC|=", Length(FAC), " |FACirred|=", Length(FACirred), "\n");
  TheResult:=RunZsolve(FACirred);
  if Length(TheResult.TheHOM) > 0 then
    Error("Inconsistency in TheHOM");
  fi;
  return TheResult.TheINH;
end;


VOR_L1_NearestPoint:=function(eRecL1, eRecCompFacet)
  local ListCandidates, EXTneigh, eEXT, eRecInt, eRecIneq;
  ListCandidates:=VOR_L1_GetCandidateNearest(eRecL1, eRecCompFacet);
  Print("|ListCandidates|=", Length(ListCandidates), "\n");
  EXTneigh:=[];
  for eEXT in ListCandidates
  do
    eRecInt:=VOR_L1_ComputeIntersection(eRecL1, eRecCompFacet, eEXT);
    if eRecInt.Answer="intersect" then
      Add(EXTneigh, eEXT);
    fi;
  od;
  return Set(EXTneigh);
end;





VOR_L1_IsComponentInequalitiesFullRank:=function(eRecL1, eRecCompFacet)
  local eRecIneq, len;
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
  len:=Length(eRecIneq.ListIneqRed);
  if len=RankMat(eRecIneq.ListIneqRed) then
    return true;
  fi;
  return false;
end;


VOR_L1_IsComponentCorrect:=function(eRecL1, eRecCompFacet)
  local ListCandidates, TheDim, eEXT, eRecInt, ListIntersect, ListEquiPt, rnkInt;
  Print("Before VOR_L1_GetCandidateNearest\n");
  ListCandidates:=VOR_L1_GetCandidateNearest(eRecL1, eRecCompFacet);
#  Print("|ListCandidates|=", Length(ListCandidates), "\n");
  TheDim:=Length(eRecCompFacet.LinSpace);
  ListEquiPt:=List(eRecCompFacet.ListEqui, x->x.ePt);
#  Print("ListEquiPt=", ListEquiPt, "\n");
  ListIntersect:=[];
  for eEXT in Difference(Set(ListCandidates), Set(ListEquiPt))
  do
    eRecInt:=VOR_L1_ComputeIntersection(eRecL1, eRecCompFacet, eEXT);
    if eRecInt.Answer="intersect" then
      rnkInt:=RankMat(eRecInt.EXT);
      if rnkInt=TheDim+1 then
        Add(ListIntersect, eEXT);
      fi;
    fi;
  od;
  if Length(ListIntersect)>0 then
    return rec(Answer:=false, ListIntersect:=ListIntersect);
  fi;
  return rec(Answer:=true, ListIntersect:=[]);
end;





VOR_L1_IsComponentCompact:=function(eRecL1, eRecCompFacet)
  local rnk, test;
  rnk:=RankMat(eRecCompFacet.ListIneqIrred);
  if rnk=Length(eRecCompFacet.LinSpace)+1 then
    test:=AreInequalitiesDefiningPolytope(eRecCompFacet.ListIneqIrred);
    if test=true then
      return true;
    else
      return false;
    fi;
  fi;
  return false;
end;


VOR_L1_IsComponentNonDegenerate:=function(eRecL1, eRecCompFacet)
  local ListIneqSimp, TheDim, TheSpace;
  ListIneqSimp:=ColumnReduction(eRecCompFacet.ListIneqIrred).EXT;
#  Print("   ListIneqSimp=", Length(ListIneqSimp), "\n");
  TheDim:=Length(ListIneqSimp[1]);
  TheSpace:=LinearDeterminedByInequalities(ListIneqSimp);
  if Length(TheSpace)=TheDim then
    return true;
  fi;
  return false;
end;





VOR_L1_FindGenericDirection:=function(eRecL1, a)
  local eVal, n, eVect, i, xVal, ListScal, TheMax, eSet, nbIter;
  eVal:=a;
  n:=eRecL1.n;
  nbIter:=0;
  while(true)
  do
    nbIter:=nbIter+1;
    eVect:=ListWithIdenticalEntries(n,0);
    Print("  eVal=", eVal, " nbIter=", nbIter, "\n");
    for i in [1..n]
    do
      xVal:=Random([-eVal..eVal]);
      eVect[i]:=xVal;
    od;
    if eVect*eVect>0 then
      ListScal:=List(eRecL1.MatrixVector, x->x*eVect);
      TheMax:=Maximum(ListScal);
      eSet:=Filtered(ListScal, x->x=TheMax);
      if Length(eSet)=1 then
        return RemoveFraction(eVect);
      fi;
      eVal:=eVal+1;
    fi;
  od;
end;



# For a list of neighbors x, we must have
#  a v.w1  <= w2.(a.v -x)
# The vector w1 is determined by v from the iteration process
# For w2, there are many possibilities a priori, so
# we iterate over all of them.
# For a non-zero vector, this gives us
# w2.x = a [ v.w2 - v.w1 ]
# a = (w2.x) / ( v.w2 - v.w1 )
VOR_L1_FindNeighboringPoints:=function(eRecL1, aRand)
  local eVect, rScalW1, rScalW2, LShort, ListVal, eShort, hVectW2, rScal, a, aVal, ePoint, ePointNorm, ListClos, aNorm, eDiff, eNorm, eScal, NShort, fVect, MaxScal, nbIter;
  eVect:=VOR_L1_FindGenericDirection(eRecL1, aRand);
  Print("eVect=", eVect, "\n");
  rScalW1:=Maximum(List(eRecL1.MatrixVector, x->x*eVect));
  LShort:=List(eRecL1.eInvBasis, x->x);
#  Print("Begin VOR_L1_FindNeighboringPoints\n");
  nbIter:=0;
  while(true)
  do
    nbIter:=nbIter+1;
    ListVal:=[];
    for eShort in LShort
    do
      for hVectW2 in eRecL1.MatrixVector
      do
        rScalW2:=hVectW2*eVect;
        if rScalW2<>rScalW1 then
          a:=(hVectW2*eShort)/(rScalW2 - rScalW1);
#          Print("a=", a, "\n");
          if a>0 then
            eDiff:=a*eVect - eShort;
            eNorm:=VOR_L1_ComputeNorm(eRecL1, eDiff);
            eScal:=hVectW2*eDiff;
            if eScal=eNorm then
              Add(ListVal, a);
            fi;
          fi;
        fi;
      od;
    od;
#    Print("eVect=", eVect, " nbIter=", nbIter, "\n");
#    Print("|ListVal|=", Length(ListVal), "\n");
    if Length(ListVal)=0 then
      NShort:=[];
      for eShort in LShort
      do
        for fVect in eRecL1.eInvBasis
        do
          Add(NShort, eShort + fVect);
        od;
      od;
      LShort:=Set(NShort);
#      Print("Now |LShort|=", Length(LShort), "\n");
    else
      aVal:=Minimum(ListVal);
#      Print("aVal=", aVal, "\n");
      ePoint:=aVal*eVect;
      ePointNorm:=aVal*rScalW1;
      ListClos:=VOR_L1_FindClosest(eRecL1, ePoint);
      aNorm:=VOR_L1_ComputeNorm(eRecL1, ePoint - ListClos[1]);
      if aNorm=ePointNorm then
        return ePoint;
      fi;
      Append(LShort, ListClos);
    fi;
  od;
end;



VOR_L1_FindNonDegeneratePairPoints:=function(eRecL1, a)
  local ePoint, ListClos, eDiff1, eDiff2, eRec1, eRec2;
  Print("Begin VOR_L1_FindNonDegeneratePairPoints\n");
  while(true)
  do
    ePoint:=VOR_L1_FindNeighboringPoints(eRecL1, a);
    ListClos:=VOR_L1_FindClosest(eRecL1, ePoint);
    if Length(ListClos)=2 then
      eDiff1:=ePoint - ListClos[1];
      eDiff2:=ePoint - ListClos[2];
      eRec1:=VOR_L1_ComputeNorm_Attain(eRecL1, eDiff1);
      eRec2:=VOR_L1_ComputeNorm_Attain(eRecL1, eDiff2);
      if Length(eRec1.ListAtt)=1 and Length(eRec2.ListAtt)=1 then
        if eRec1.ListAtt<>eRec2.ListAtt then
          return ePoint;
        fi;
      fi;
    fi;
  od;
end;


VOR_L1_IsFeasible:=function(eRecL1, eRecCompFacet, ePoint)
  local eRecIneq, eSol, eSolExp, ListScal, nbIneq, iRec, eEqui, eRelevant, eScal1, eScal2, eIneqType;
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
  nbIneq:=Length(eRecIneq.ListIneqRed);
  eSol:=SolutionMat(eRecCompFacet.LinSpace, ePoint - eRecCompFacet.SinglePt);
  eSolExp:=Concatenation([1], eSol);
  ListScal:=List(eRecIneq.ListIneqRed, x->x*eSolExp);
  for iRec in [1..nbIneq]
  do
    eIneqType:=eRecIneq.ListIneqType[iRec];
    if eIneqType.type="nearest" then
      eEqui:=eRecCompFacet.ListEqui[1];
      eRelevant:=eRecCompFacet.ListRelevant[eIneqType.iRelevant];
      eScal1:=eRecL1.MatrixVector[eEqui.posIneq]*(ePoint - eEqui.ePt);
      eScal2:=eRecL1.MatrixVector[eRelevant.posIneq]*(ePoint - eRelevant.ePt);
      if eScal2 - eScal1<>ListScal[iRec] then
        Print("Inconsistency in eScal1, eScal2\n");
        return false;
      fi;
    fi;
  od;
  if Minimum(ListScal)<0 then
    Print("One bug to be solved\n");
    return false;
  fi;
  return true;
end;

VOR_L1_GetLinSpace:=function(eRecL1, ListEqui)
  local n, eLine, iEqui, nbEqui, ListLine;
  n:=eRecL1.n;
  ListLine:=[];
  nbEqui:=Length(ListEqui);
  for iEqui in [2..nbEqui]
  do
    eLine:=eRecL1.MatrixVector[ListEqui[iEqui].posIneq] - eRecL1.MatrixVector[ListEqui[1].posIneq];
    Add(ListLine, RemoveFraction(eLine));
  od;
  if Length(ListLine)=0 then
    return IdentityMat(n);
  fi;
  return NullspaceIntMat(TransposedMat(ListLine));
end;




VOR_L1_TestMultiplicityDegeneracy:=function(eRecL1, LinSpace, eRec)
  local ListVect, eVect, eVal, IsCorrect;
  ListVect:=[];
  for eVal in eRec.ListAtt
  do
    eVect:=List(LinSpace, x->x*eRecL1.MatrixVector[eVal]);
    Add(ListVect, eVect);
  od;
  IsCorrect:=Length(Set(ListVect))=1;
  return rec(ListVect:=ListVect, IsCorrect:=IsCorrect);
end;

VOR_L1_EliminateUnneeded:=function(eRecL1, eRecCompFacet)
  local eRecIneq, ListIneq, SetIneq, SetIneqRed, CorrIdx, eIneq, eSet, ListIRelevant, iIneq, eType, SetRelevant;
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
  ListIneq:=List(eRecIneq.ListIneqRed, RemoveFraction);
  SetIneq:=Set(ListIneq);
  SetIneqRed:=RemoveRedundancyByDualDescription(SetIneq);
  CorrIdx:=[];
  for eIneq in SetIneqRed
  do
    eSet:=Filtered([1..Length(ListIneq)], x->ListIneq[x]=eIneq);
    Append(CorrIdx, eSet);
  od;
  ListIRelevant:=[];
  for iIneq in CorrIdx
  do
    eType:=eRecIneq.ListIneqType[iIneq];
    Add(ListIRelevant, eType.iRelevant);
  od;
  SetRelevant:=Set(ListIRelevant);
  Print("|ListRelevant|=", Length(eRecCompFacet.ListRelevant), " |SetRelevant|=", Length(SetRelevant), "\n");
  return SetRelevant;
end;


VOR_L1_ClearCompFacet:=function(eRecL1, eRecCompFacet)
  local ListRelevant, fRecCompFacet, eRecIneq, ListIneqNoFrac, ListIneqIrred, ListRelevantPt, testComp, eRecTest, EXTvertices, EXTneigh, IsMatching, ListBad, eSet, ListVect, ReducedListRelevant, eIneq, eInt;
  ListRelevant:=eRecCompFacet.ListRelevant;
  while(true)
  do
    fRecCompFacet:=rec(SinglePt:=eRecCompFacet.SinglePt, 
                       LinSpace:=eRecCompFacet.LinSpace, 
                       ListEqui:=eRecCompFacet.ListEqui, 
                       ListRelevant:=ListRelevant);
    eRecIneq:=VOR_L1_GetInequalities(eRecL1, fRecCompFacet);
    ListIneqNoFrac:=List(eRecIneq.ListIneqRed, RemoveFraction);
    ListIneqIrred:=RemoveRedundancyByDualDescription(ListIneqNoFrac);
    fRecCompFacet.ListIneqIrred:=ListIneqIrred;
    ListRelevantPt:=List(ListRelevant, x->x.ePt);
    testComp:=VOR_L1_IsComponentCompact(eRecL1, fRecCompFacet);
    if testComp=false then
      return fail;
    fi;
    if VOR_L1_IsComponentNonDegenerate(eRecL1, fRecCompFacet)=false then
      return rec(Answer:=false, reason:="Death by degenerate face");
    fi;
    eRecTest:=VOR_L1_IsComponentCorrect(eRecL1, fRecCompFacet);
    if eRecTest.Answer=false then
      return fail;
    fi;
    EXTvertices:=Set(VOR_L1_GetVertices(eRecL1, fRecCompFacet).EXT);
    EXTneigh:=VOR_L1_NearestPoint(eRecL1, fRecCompFacet);
    Print("|EXTneigh|=", Length(EXTneigh), "\n");
    if IsSubset(Set(ListRelevantPt), Set(EXTneigh))=false then
      return rec(Answer:=fail);
    fi;
    #
    IsMatching:=true;
    ListBad:=[];
    for eIneq in ListIneqIrred
    do
      eSet:=Filtered([1..Length(ListIneqNoFrac)], x->ListIneqNoFrac[x]=eIneq);
      ListVect:=Set(List(eSet, x->ListRelevant[eRecIneq.ListIneqType[x].iRelevant].ePt));
      eInt:=Intersection(ListVect, EXTneigh);
      if Length(eInt)=0 then
        IsMatching:=false;
        Append(ListBad, ListRelevant{eSet});
      fi;
    od;
    if IsMatching then
      ReducedListRelevant:=Filtered(ListRelevant, x->Position(EXTneigh, x.ePt)<>fail);
      fRecCompFacet.ListRelevant:=ReducedListRelevant;
      return rec(Answer:=true, eRecCompFacet:=fRecCompFacet);
    fi;
    ListRelevant:=Difference(Set(ListRelevant), Set(ListBad));
  od;
end;


VOR_L1_HyperplaneTests:=function(eRecL1, eRecCompFacet)
  local EXTvertices, eHyper, eRecGcd, eGcd, MinVal, MaxVal, ListVal, eUpp;
  EXTvertices:=Set(VOR_L1_GetVertices(eRecL1, eRecCompFacet).EXT);
#  Print("|ListHyperplane|=", Length(eRecL1.ListHyperplane), "\n");
#  Print("ListHyperplane=", eRecL1.ListHyperplane, "\n");
  for eHyper in eRecL1.ListHyperplane
  do
    eRecGcd:=GcdVector(eHyper);
    eGcd:=eRecGcd.TheGcd;
    ListVal:=List(EXTvertices, x->x*eHyper);
    MinVal:=Minimum(ListVal);
    MaxVal:=Maximum(ListVal);
#    Print("eGcd=", eGcd, " MinVal=", MinVal, " MaxVal=", MaxVal, " eHyper=", eHyper, "\n");
    if IsInt(MinVal/eGcd)=true then
      if MaxVal>MinVal + eGcd then
        Print("Fail case 1\n");
        return false;
      fi;
    else
      eUpp:=UpperInteger(MinVal/eGcd);
      if eUpp<MaxVal then
        Print("Fail case 2\n");
        return false;
      fi;
    fi;
  od;
  return true;
end;


VOR_L1_ClearCompFacet_PlanB:=function(eRecL1, eRecCompFacet)
  local ListRelevantPt, testComp, eRecTest, EXTvertices, EXTneigh, SetRelevant, fRecCompFacet;
  ListRelevantPt:=List(eRecCompFacet.ListRelevant, x->x.ePt);
  testComp:=VOR_L1_IsComponentCompact(eRecL1, eRecCompFacet);
  if testComp=false then
    return rec(Answer:=fail, reason:="fail at compacity");
  fi;
  if VOR_L1_IsComponentNonDegenerate(eRecL1, eRecCompFacet)=false then
    return rec(Answer:=false, reason:="Death by degenerate face");
  fi;
  eRecTest:=VOR_L1_IsComponentCorrect(eRecL1, eRecCompFacet);
  if eRecTest.Answer=false then
    return rec(Answer:=fail, reason:="fail at correctness");
  fi;
  EXTvertices:=Set(VOR_L1_GetVertices(eRecL1, eRecCompFacet).EXT);
  EXTneigh:=VOR_L1_NearestPoint(eRecL1, eRecCompFacet);
  Print("|EXTneigh|=", Length(EXTneigh), "\n");
  if IsSubset(Set(ListRelevantPt), Set(EXTneigh))=false then
    return rec(Answer:=fail, reason:="fail at ListRelevantPt inclusion");
  fi;
  #
  if VOR_L1_HyperplaneTests(eRecL1, eRecCompFacet)=false then
    return rec(Answer:=fail, reason:="fail at hyperplanes");
  fi;
  SetRelevant:=VOR_L1_EliminateUnneeded(eRecL1, eRecCompFacet);
  fRecCompFacet:=rec(SinglePt:=eRecCompFacet.SinglePt, 
                     LinSpace:=eRecCompFacet.LinSpace, 
                     ListEqui:=eRecCompFacet.ListEqui, 
                     ListRelevant:=eRecCompFacet.ListRelevant{SetRelevant},
                     ListIneqIrred:=eRecCompFacet.ListIneqIrred);
  return rec(Answer:=true, eRecCompFacet:=fRecCompFacet);
end;





VOR_L1_GetComponentFromPoint:=function(eRecL1, ePoint, minSizeClos, soughtDimLin)
  local n, UpdateFamily, ResetFamily, ListClos, eDiff1, eDiff2, eRec1, eRec2, eNorm1, eNorm2, CurrentFamily, posIneq1, posIneq2, LinSpace, eEqui1, eEqui2, ListEqui, ListRelevant, eVect, eDiff, ListScal, MaxScal, eSet, eRelevant, eRecCompFacet, test, a, eVectDiff, testComp, eRecTest, EXTneigh, ListRelevantPt, eEqui, posIneq, eRec, ePtClos, CorrCompFacet, eRecDeg, ListEquiTot, LinSpaceTot, SetRelevant, fRecCompFacet, eRecIneq, ListIneqIrred, DimRel, UpdateDualDesc, IsVectorRelevant, EXTfac, i, nbUpdate;
  Print("Begin VOR_L1_GetComponentFromPoint\n");
  ListClos:=VOR_L1_FindClosest(eRecL1, ePoint);
  n:=eRecL1.n;
  if Length(ePoint)<>n then
    Error("Wrong length of vector in input");
  fi;
  a:=1;
  UpdateFamily:=function()
    local NCurrentFamily, eVect, fVect, SetFamily, ListNorm, ePerm;
    NCurrentFamily:=[];
    for eVect in CurrentFamily
    do
      for fVect in eRecL1.eInvBasis
      do
        Add(NCurrentFamily, eVect + fVect);
      od;
    od;
    SetFamily:=Set(NCurrentFamily);
    ListNorm:=List(SetFamily, x->VOR_L1_ComputeNorm(eRecL1, ePoint - x));
    ePerm:=SortingPerm(ListNorm);
    CurrentFamily:=Permuted(SetFamily, ePerm);
  end;
  CurrentFamily:=List(ListClos, x->x);
  for i in [1..3]
  do
    UpdateFamily();
  od;
#  Print("ePoint=", ePoint, "\n");
#  Print("Now iterating\n");
  if Length(ListClos) < minSizeClos then
    return rec(Answer:=false, reason:="ListClos is too small", ListClos:=ListClos);
  fi;
  ListEqui:=[];
  ListEquiTot:=[];
#  Print("ListClos=", ListClos, "\n");
  for ePtClos in ListClos
  do
    eDiff:=ePoint - ePtClos;
    eRec:=VOR_L1_ComputeNorm_Attain(eRecL1, eDiff);
    posIneq:=eRec.ListAtt[1];
    eEqui:=rec(ePt:=ePtClos, posIneq:=posIneq);
    Add(ListEqui, eEqui);
    for posIneq in eRec.ListAtt
    do
      eEqui:=rec(ePt:=ePtClos, posIneq:=posIneq);
      Add(ListEquiTot, eEqui);
    od;
  od;
  LinSpace:=VOR_L1_GetLinSpace(eRecL1, ListEqui);
  LinSpaceTot:=VOR_L1_GetLinSpace(eRecL1, ListEquiTot);
  if Length(LinSpace)<>Length(LinSpaceTot) then
    return rec(Answer:=false, reason:="Too large eSet inducing artificial space splitting");
  fi;
  if Length(LinSpace)<soughtDimLin then
    return rec(Answer:=false, reason:="Death by too small LinSpace");
  fi;
  if Length(LinSpace)>soughtDimLin then
    return rec(Answer:=false, reason:="Death by too large LinSpace", LinSpace:=LinSpace, ListEqui:=ListEqui);
  fi;
  DimRel:=RankMat(LinSpace)+1;
  while(true)
  do
    ListRelevant:=[];
    ListRelevantPt:=[];
#    Print("|CurrentFamily|=", Length(CurrentFamily), "\n");
    EXTfac:=[];
    ListIneqIrred:=[];
    IsVectorRelevant:=function(eVect)
      local eDiff, eRec, posIneq, eRecDeg, eRelevant, eRecCompFacetDummy, eRecIneqDummy, eEXT, eIneq;
      eDiff:=ePoint - eVect;
      eRec:=VOR_L1_ComputeNorm_Attain(eRecL1, eDiff);
      posIneq:=eRec.ListAtt[1];
      eRecDeg:=VOR_L1_TestMultiplicityDegeneracy(eRecL1, LinSpace, eRec);
      eRelevant:=rec(ePt:=eVect, posIneq:=posIneq);
      eRecCompFacetDummy:=rec(SinglePt:=ePoint,
                       LinSpace:=LinSpace,
                       ListEqui:=ListEqui,
                       ListRelevant:=[eRelevant]);
      eRecIneqDummy:=VOR_L1_GetInequalities(eRecL1, eRecCompFacetDummy);
      for eEXT in EXTfac
      do
        for eIneq in eRecIneqDummy.ListIneqRed
        do
          if eIneq*eEXT < 0 then
            return true;
          fi;
        od;
      od;
      return false;
    end;
    nbUpdate:=0;
    for eVect in CurrentFamily
    do
      eDiff:=ePoint - eVect;
      eRec:=VOR_L1_ComputeNorm_Attain(eRecL1, eDiff);
      posIneq:=eRec.ListAtt[1];
#      Print("eVect=", eVect, " posIneq=", posIneq, " ListAtt=", eRec.ListAtt, "\n");
      eRecDeg:=VOR_L1_TestMultiplicityDegeneracy(eRecL1, LinSpace, eRec);
      eRelevant:=rec(ePt:=eVect, posIneq:=posIneq);
      UpdateDualDesc:=false;
      if PersoRankMat(ListIneqIrred) < DimRel then
        UpdateDualDesc:=true;
        if eRecDeg.IsCorrect=false then
          return rec(Answer:=false, reason:="eSet cause splitting", eDiff:=eDiff, eRec:=eRec, eRecDeg:=eRecDeg);
        fi;
      else
        if IsVectorRelevant(eVect) then
          UpdateDualDesc:=true;
          if eRecDeg.IsCorrect=false then
            return rec(Answer:=false, reason:="eSet cause splitting", eDiff:=eDiff, eRec:=eRec, eRecDeg:=eRecDeg);
          fi;
        fi;
      fi;
      Add(ListRelevant, eRelevant);
      Add(ListRelevantPt, eVect);
      eRecCompFacet:=rec(SinglePt:=ePoint,
                         LinSpace:=LinSpace,
                         ListEqui:=ListEqui,
                         ListRelevant:=ListRelevant);
      if UpdateDualDesc=true then
        nbUpdate:=nbUpdate+1;
        eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
        if PersoRankMat(eRecIneq.ListIneqRed) = DimRel then
          ListIneqIrred:=RemoveRedundancyByDualDescription(eRecIneq.ListIneqRed);
          EXTfac:=DualDescription(ListIneqIrred);
        fi;
      fi;
    od;
    eRecCompFacet.ListIneqIrred:=ListIneqIrred;
    test:=VOR_L1_ClearCompFacet_PlanB(eRecL1, eRecCompFacet);
#    Print("test=", test, "\n");
    if test.Answer<>fail then
      return test;
    fi;
    UpdateFamily();
  od;
end;


VOR_L1_TestConsistencySingleCell:=function(eRecL1, eRecCompCell)
  local n, minSizeClos, soughtDimLin, eRecEXT, EXTrel, eSumVect, eSum, eEXT, eVal, ePoint, eRecAnswer, eRecEXTb, EXTrelB, iter;
  n:=eRecL1.n;
  minSizeClos:=1;
  soughtDimLin:=n;
  eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompCell);
  EXTrel:=Set(eRecEXT.EXT);
  eSumVect:=ListWithIdenticalEntries(n,0);
  eSum:=0;
  for eEXT in eRecEXT.EXT
  do
    eVal:=Random([1..20]);
    eSumVect:=eSumVect + eVal*eEXT;
    eSum:=eSum + eVal;
  od;
  ePoint:=eSumVect/eSum;
  #
  eRecAnswer:=VOR_L1_GetComponentFromPoint(eRecL1, ePoint, minSizeClos, soughtDimLin);
  if eRecAnswer.Answer=true then
    eRecEXTb:=VOR_L1_GetVertices(eRecL1, eRecAnswer.eRecCompFacet);
    EXTrelB:=Set(eRecEXTb.EXT);
    if EXTrelB<>EXTrel then
      Error("Unfortunately, that is inconsistency");
    fi;
  fi;
end;



# rec(SinglePt:=....
#     LinSpace:=.....
#     ListEqui:=[fRec1, fRec2, ....], 
#     ListRelevant:=[eRec1, eRec2, .....])
# With eRec1, eRec2, .... being of the form
# rec(ePt:=.....  , posIneq:=idx)
#
# We enforce the strict rule that any points that is in 
# the neighbor satisfies an inequality  l1(x-v)>=l2(x-v)
VOR_L1_GetInitialComponent:=function(eRecL1)
  local n, a, ePoint, eRecAnswer, minSizeClos, soughtDimLin;
  Print("Begin VOR_L1_GetInitialComponent\n");
  a:=1;
  n:=eRecL1.n;
  minSizeClos:=2;
  soughtDimLin:=n-1;
  while(true)
  do
    ePoint:=VOR_L1_FindNonDegeneratePairPoints(eRecL1, a);
    Print("ePoint=", ePoint, "\n");
    eRecAnswer:=VOR_L1_GetComponentFromPoint(eRecL1, ePoint, minSizeClos, soughtDimLin);
    if eRecAnswer.Answer=true then
      return eRecAnswer.eRecCompFacet;
    fi;
    if eRecAnswer.Answer=false and eRecAnswer.reason="ListClos is too small" then
      Error("Error in eRecAnswer 1");
    fi;
    a:=a+1;
  od;
end;






VOR_L1_DirectionTest:=function(eRecL1, eRecCompFacet, ePt, eDirVect)
  local eRecIneq, TheDim, eSolVect, eSolPt, ePtRed, eIneq, eIneqR;
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
  TheDim:=Length(eRecCompFacet.LinSpace);
  Print("eDirVect=", eDirVect, "\n");
  Print("LinSpace=", eRecCompFacet.LinSpace, "\n");
  eSolVect:=SolutionMat(eRecCompFacet.LinSpace, eDirVect);
  Print("eSolVect=", eSolVect, "\n");
  eSolPt:=SolutionMat(eRecCompFacet.LinSpace, ePt - eRecCompFacet.SinglePt);
  ePtRed:=Concatenation([1], eSolPt);
  Print("eRecIneq=", eRecIneq, "\n");
  for eIneq in eRecIneq.ListIneqRed
  do
    if ePtRed*eIneq=0 then
      eIneqR:=eIneq{[2..TheDim+1]};
      if eIneqR*eSolVect < 0 then
        Print("Kill eIneq=", eIneq, "\n");
        return false;
      fi;
    fi;
  od;
  return true;
end;



VOR_L1_TestViolationProperty:=function(eRecL1, ListEqui, eCent, eDirVect, eTestPt, eCandPt)
  local eDiff, eRecAtt, LinSpace, TheDim, posIneq, eRecCompFacet, eRecIneq, eSol, eIneq, eIneqR, len;
  eDiff:=eTestPt - eCandPt;
  eRecAtt:=VOR_L1_ComputeNorm_Attain(eRecL1, eDiff);
  len:=Length(eRecAtt.ListAtt);
  Print("len=", len, "\n");
  #
  posIneq:=eRecAtt.ListAtt[1];
  LinSpace:=VOR_L1_GetLinSpace(eRecL1, ListEqui);
  TheDim:=Length(LinSpace);
  eRecCompFacet:=rec(SinglePt:=eCent, 
                     LinSpace:=LinSpace, 
                     ListEqui:=ListEqui, 
                     ListRelevant:=[rec(ePt:=eCandPt, posIneq:=posIneq)]);
  if VOR_L1_IsFeasible(eRecL1, eRecCompFacet, eCent) then
    return VOR_L1_DirectionTest(eRecL1, eRecCompFacet, eCent, eDirVect);
  fi;
  return fail;
end;

VOR_L1_GetCompletionFromGerm:=function(eRecL1, ListEqui, eCent, eDirVect)
  local n, hShift, eTestPt, eRecAnswer, eRecCompFacetTest, eRecCompFacet, ePtClos, test, LinSpace, minSizeClos, soughtDimLin;
  n:=eRecL1.n;
  hShift:=1;
  LinSpace:=VOR_L1_GetLinSpace(eRecL1, ListEqui);
  if Length(LinSpace)=n then
    return fail;
  fi;
  minSizeClos:=2;
  soughtDimLin:=n-1;
  Print("eCent=", eCent, " eDirVect=", eDirVect, "\n");
  Print("ListEqui=", ListEqui, "\n");
  Print("LinSpace=", LinSpace, "\n");
  eRecCompFacetTest:=rec(SinglePt:=eCent, LinSpace:=LinSpace, ListEqui:=ListEqui, ListRelevant:=ListEqui);
  if VOR_L1_DirectionTest(eRecL1, eRecCompFacetTest, eCent, eDirVect)=false then
    Print("Fail case 1\n");
    return fail;
  fi;
  while(true)
  do
    eTestPt:=eCent + hShift*eDirVect;
    Print("eCent=", eCent, "  hShift=", hShift, " eDirVect=", eDirVect, "\n");
    Print("ListEqui=", ListEqui, "\n");
    eRecAnswer:=VOR_L1_GetComponentFromPoint(eRecL1, eTestPt, minSizeClos, soughtDimLin);
    if eRecAnswer.Answer=true then
      eRecCompFacet:=eRecAnswer.eRecCompFacet;
      if IsSubset(Set(eRecCompFacet.ListEqui), Set(ListEqui)) then
        return eRecCompFacet;
      else
        ePtClos:=eRecCompFacet.ListEqui[1].ePt;
        test:=VOR_L1_TestViolationProperty(eRecL1, ListEqui, eCent, eDirVect, eTestPt, ePtClos);
        if test=false then
          return fail;
        fi;
      fi;
    else
      Print("reason=", eRecAnswer.reason, "\n");
      if eRecAnswer.reason="ListClos is too small" then
        ePtClos:=eRecAnswer.ListClos[1];
        Print("ListClos too small, doing tests\n");
        test:=VOR_L1_TestViolationProperty(eRecL1, ListEqui, eCent, eDirVect, eTestPt, ePtClos);
        if test=false then
          return fail;
        fi;
      fi;
    fi;
    if hShift<1/100 then
      Error("Please debug from here");
    fi;
    hShift:=hShift/2;
    Print("Now hShift=", hShift, "\n");
  od;
end;

VOR_L1_GetInitialCell:=function(eRecL1)
  local n, a, ePoint, eRecAnswer, minSizeClos, ePointRed, soughtDimLin;
  Print("Begin VOR_L1_GetInitialCell\n");
  n:=eRecL1.n;
  a:=1;
  minSizeClos:=1;
  soughtDimLin:=n;
  while(true)
  do
    ePoint:=VOR_L1_FindNonDegeneratePairPoints(eRecL1, a);
    ePointRed:=ePoint/2;
    Print("ePointRed=", ePointRed, "\n");
    eRecAnswer:=VOR_L1_GetComponentFromPoint(eRecL1, ePointRed, minSizeClos, soughtDimLin);
    if eRecAnswer.Answer=true then
      return eRecAnswer.eRecCompFacet;
    fi;
    Print("eRecAnswer=", eRecAnswer, "\n");
    a:=a+1;
  od;
end;


VOR_L1_PrintListEqui:=function(ListEqui)
  local nbEqui, iEqui, eEqui;
  nbEqui:=Length(ListEqui);
  for iEqui in [1..nbEqui]
  do
    if iEqui>1 then
      Print(",");
    fi;
    eEqui:=ListEqui[iEqui];
    Print("rec(", eEqui.ePt, " p=", eEqui.posIneq, ")");
  od;
  Print("\n");
end;




VOR_L1_GetFlippings_V1:=function(eRecL1, eRecCompFacet, eRecIneq, EXTinc, lSet)
  local n, TheDim, NewListFaces, FuncInsertCompFacet, ListPtEqui, eCent, ListDiff, eIneqFace, i, eIneqType, eEqui, fEqui, LConn, eConnSel, posEqui, SetRec, pos1, pos2, GRA, NewListEqui, ePair, eRec1, eRec2, eRelevant, iRelevant, iIneq, jIneq, ListEquivalencePair, HaveDomNorm, nbEqui, eRec, nbRec;
  n:=eRecL1.n;
  TheDim:=Length(eRecCompFacet.LinSpace);
  NewListFaces:=[];
  eCent:=Isobarycenter(EXTinc);
  Print("eCent=", eCent, "\n");
  FuncInsertCompFacet:=function(NewListEqui)
    local eSol, eSign, eFlip, fDirVect, LinSpace, eDirVect;
    LinSpace:=VOR_L1_GetLinSpace(eRecL1, NewListEqui);
    if Length(LinSpace)<>n and NewListEqui[1].ePt <>NewListEqui[2].ePt then
      eDirVect:=First(LinSpace, x->SolutionMat(ListDiff, x)=fail);
      eSol:=SolutionMat(eRecCompFacet.LinSpace, eDirVect);
      if eSol=fail then
        for eSign in [-1,1]
        do
          eFlip:=VOR_L1_GetCompletionFromGerm(eRecL1, NewListEqui, eCent, eSign*eDirVect);
          if eFlip<>fail then
            Add(NewListFaces, eFlip);
          fi;
        od;
      else
        if eIneqFace*eSol > 0 then
          fDirVect:=-eDirVect;
        else
          fDirVect:=eDirVect;
        fi;
        eFlip:=VOR_L1_GetCompletionFromGerm(eRecL1, NewListEqui, eCent, fDirVect);
        if eFlip<>fail then
          Add(NewListFaces, eFlip);
        fi;
      fi;
    fi;
  end;
  ListPtEqui:=List(eRecCompFacet.ListEqui, x->x.ePt);
  ListDiff:=List(EXTinc, x->x - EXTinc[1]);
  eIneqFace:=eRecIneq.ListIneqRed{[2..TheDim+1]};
  #
  # First new ListEqui can arise from any inequality
  # becoming equality
  #
  for i in lSet
  do
    eIneqType:=eRecIneq.ListIneqType[i];
    if eIneqType.type="nearest" then
      for eEqui in eRecCompFacet.ListEqui
      do
        NewListEqui:=[eEqui, eRecCompFacet.ListRelevant[eIneqType.iRelevant]];
        FuncInsertCompFacet(NewListEqui);
      od;
    fi;
  od;
  #
  # Second any "dom norm" inequality means that we can continue
  # in the same direction
  #
  HaveDomNorm:=false;
  for i in lSet
  do
    eIneqType:=eRecIneq.ListIneqType[i];
    if eIneqType.type="dom norm" then
      HaveDomNorm:=true;
    fi;
  od;
  if HaveDomNorm then
    FuncInsertCompFacet(eRecCompFacet.ListEqui);
  fi;
  #
  # Third any switch of inequality can present a potential
  # switch in the ListEqui
  #
  ListEquivalencePair:=[];
  eEqui:=eRecCompFacet.ListEqui[1];
  nbEqui:=Length(eRecCompFacet.ListEqui);
  for fEqui in eRecCompFacet.ListEqui{[2..nbEqui]}
  do
    ePair:=[eEqui, fEqui];
    Add(ListEquivalencePair, ePair);
  od;
  for i in lSet
  do
    eIneqType:=eRecIneq.ListIneqType[i];
    if eIneqType.type="dom norm" then
      iIneq:=eIneqType.iIneq;
      jIneq:=eIneqType.jIneq;
      iRelevant:=eIneqType.iRelevant;
      eRelevant:=eRecCompFacet.ListRelevant[iRelevant];
      eRec1:=rec(ePt:=eRelevant.ePt, posIneq:=iIneq);
      eRec2:=rec(ePt:=eRelevant.ePt, posIneq:=jIneq);
      ePair:=[eRec1, eRec2];
      Add(ListEquivalencePair, ePair);
    fi;
    if eIneqType.type="nearest" then
      iRelevant:=eIneqType.iRelevant;
      eRelevant:=eRecCompFacet.ListRelevant[iRelevant];
      ePair:=[eEqui, eRelevant];
      Add(ListEquivalencePair, ePair);
    fi;
  od;
  SetRec:=Set([]);
  for ePair in ListEquivalencePair
  do
    for eRec in ePair
    do
      AddSet(SetRec, eRec);
    od;
  od;
#  Print("SetRec=", SetRec, "\n");
  nbRec:=Length(SetRec);
  GRA:=NullGraph(Group(()), nbRec);
  for ePair in ListEquivalencePair
  do
    pos1:=Position(SetRec, ePair[1]);
    pos2:=Position(SetRec, ePair[2]);
    if pos1<>pos2 then
      AddEdgeOrbit(GRA, [pos1, pos2]);
      AddEdgeOrbit(GRA, [pos2, pos1]);
    fi;
  od;
  LConn:=ConnectedComponents(GRA);
  posEqui:=Position(SetRec, eEqui);
  eConnSel:=First(LConn, x->Position(x, posEqui)<>fail);
  for NewListEqui in Combinations(SetRec{eConnSel}, 2)
  do
    FuncInsertCompFacet(NewListEqui);
  od;
  return NewListFaces;
end;

VOR_L1_IsLinSpaceContained:=function(LinSpace1, LinSpace2)
  local eVect1;
  for eVect1 in LinSpace1
  do
    if SolutionMat(LinSpace2, eVect1)=fail then
      return false;
    fi;
  od;
  return true;
end;

VOR_L1_IsLinSpaceEqual:=function(LinSpace1, LinSpace2)
  if VOR_L1_IsLinSpaceContained(LinSpace1, LinSpace2)=false then
    return false;
  fi;
  if VOR_L1_IsLinSpaceContained(LinSpace2, LinSpace1)=false then
    return false;
  fi;
  return true;
end;


VOR_L1_GetFlippings:=function(eRecL1, eRecCompFacet, eRecIneq, EXTinc, lSet)
  local n, TheDim, NewListFaces, FuncInsertCompFacet, ListPtEqui, eCent, ListDiff, eIneqFace, i, eIneqType, eEqui, fEqui, LConn, eConnSel, posEqui, SetRec, pos1, pos2, GRA, NewListEqui, ePair, eRec1, eRec2, eRelevant, iRelevant, iIneq, jIneq, ListEquivalencePair, HaveDomNorm, nbEqui, eRec, nbRec;
  n:=eRecL1.n;
  TheDim:=Length(eRecCompFacet.LinSpace);
  NewListFaces:=[];
  eCent:=Isobarycenter(EXTinc);
  Print("eCent=", eCent, "\n");
  FuncInsertCompFacet:=function(NewListEqui)
    local eSol, eSign, eFlip, fDirVect, LinSpace, eDirVect;
    LinSpace:=VOR_L1_GetLinSpace(eRecL1, NewListEqui);
    if Length(LinSpace)<>n and NewListEqui[1].ePt <>NewListEqui[2].ePt then
      eDirVect:=First(LinSpace, x->SolutionMat(ListDiff, x)=fail);
      eSol:=SolutionMat(eRecCompFacet.LinSpace, eDirVect);
      if eSol=fail then
        for eSign in [-1,1]
        do
          eFlip:=VOR_L1_GetCompletionFromGerm(eRecL1, NewListEqui, eCent, eSign*eDirVect);
          if eFlip<>fail then
            Add(NewListFaces, eFlip);
          fi;
        od;
      else
        if eIneqFace*eSol > 0 then
          fDirVect:=-eDirVect;
        else
          fDirVect:=eDirVect;
        fi;
        eFlip:=VOR_L1_GetCompletionFromGerm(eRecL1, NewListEqui, eCent, fDirVect);
        if eFlip<>fail then
          Add(NewListFaces, eFlip);
        fi;
      fi;
    fi;
  end;
  ListPtEqui:=List(eRecCompFacet.ListEqui, x->x.ePt);
  ListDiff:=List(EXTinc, x->x - EXTinc[1]);
  eIneqFace:=eRecIneq.ListIneqRed{[2..TheDim+1]};
  #
  # First new ListEqui can arise from any inequality
  # becoming equality
  #
  for i in lSet
  do
    eIneqType:=eRecIneq.ListIneqType[i];
    if eIneqType.type="nearest" then
      for eEqui in eRecCompFacet.ListEqui
      do
        NewListEqui:=[eEqui, eRecCompFacet.ListRelevant[eIneqType.iRelevant]];
        FuncInsertCompFacet(NewListEqui);
      od;
    fi;
  od;
  #
  # Second any "dom norm" inequality means that we can continue
  # in the same direction
  #
  HaveDomNorm:=false;
  for i in lSet
  do
    eIneqType:=eRecIneq.ListIneqType[i];
    if eIneqType.type="dom norm" then
      HaveDomNorm:=true;
    fi;
  od;
  if HaveDomNorm then
    FuncInsertCompFacet(eRecCompFacet.ListEqui);
  fi;
  #
  # Third any switch of inequality can present a potential
  # switch in the ListEqui
  #
  ListEquivalencePair:=[];
  eEqui:=eRecCompFacet.ListEqui[1];
  nbEqui:=Length(eRecCompFacet.ListEqui);
  for fEqui in eRecCompFacet.ListEqui{[2..nbEqui]}
  do
    ePair:=[eEqui, fEqui];
    Add(ListEquivalencePair, ePair);
  od;
  for i in lSet
  do
    eIneqType:=eRecIneq.ListIneqType[i];
    if eIneqType.type="dom norm" then
      iIneq:=eIneqType.iIneq;
      jIneq:=eIneqType.jIneq;
      iRelevant:=eIneqType.iRelevant;
      eRelevant:=eRecCompFacet.ListRelevant[iRelevant];
      eRec1:=rec(ePt:=eRelevant.ePt, posIneq:=iIneq);
      eRec2:=rec(ePt:=eRelevant.ePt, posIneq:=jIneq);
      ePair:=[eRec1, eRec2];
      Add(ListEquivalencePair, ePair);
    fi;
    if eIneqType.type="nearest" then
      iRelevant:=eIneqType.iRelevant;
      eRelevant:=eRecCompFacet.ListRelevant[iRelevant];
      ePair:=[eEqui, eRelevant];
      Add(ListEquivalencePair, ePair);
    fi;
  od;
  SetRec:=Set([]);
  for ePair in ListEquivalencePair
  do
    for eRec in ePair
    do
      AddSet(SetRec, eRec);
    od;
  od;
#  Print("SetRec=", SetRec, "\n");
  nbRec:=Length(SetRec);
  GRA:=NullGraph(Group(()), nbRec);
  for ePair in ListEquivalencePair
  do
    pos1:=Position(SetRec, ePair[1]);
    pos2:=Position(SetRec, ePair[2]);
    if pos1<>pos2 then
      AddEdgeOrbit(GRA, [pos1, pos2]);
      AddEdgeOrbit(GRA, [pos2, pos1]);
    fi;
  od;
  LConn:=ConnectedComponents(GRA);
  posEqui:=Position(SetRec, eEqui);
  eConnSel:=First(LConn, x->Position(x, posEqui)<>fail);
  for NewListEqui in Combinations(SetRec{eConnSel}, 2)
  do
    FuncInsertCompFacet(NewListEqui);
  od;
  return NewListFaces;
end;



VOR_L1_GetAllFlips:=function(eRecL1, eRecCompFacet)
  local TheDim, eRecIneq, EXTred, ListInc, SetInc, ListFlip, eInc, EXTinc, rnk, lSet, NewFlipFacet, eRecStab, O, eO;
  TheDim:=Length(eRecCompFacet.LinSpace);
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompFacet);
  eRecStab:=VOR_L1_AutomorphismCompFacet(eRecL1, eRecCompFacet);
  EXTred:=eRecStab.EXTred;
  ListInc:=List(eRecIneq.ListIneqRed, x->Filtered([1..Length(EXTred)], y->x*EXTred[y]=0));
  SetInc:=Set(ListInc);
  O:=Orbits(eRecStab.GRPext, SetInc, OnSets);
  ListFlip:=[];
  for eO in O
  do
    eInc:=eO[1];
    EXTinc:=eRecStab.EXT{eInc};
    if Length(EXTinc)=0 then
      rnk:=0;
    else
      rnk:=RankMat(EXTinc);
    fi;
    if rnk=TheDim then
      lSet:=Filtered([1..Length(ListInc)], x->ListInc[x]=eInc);
      NewFlipFacet:=VOR_L1_GetFlippings(eRecL1, eRecCompFacet, eRecIneq, EXTinc, lSet);
      Append(ListFlip, NewFlipFacet);
    fi;
  od;
  return ListFlip;
end;





VOR_L1_FullEnumeration:=function(eRecL1)
  local ListRecCompFacet, ListStatus, FuncInsert, IsFinished, nbRec, iRec, ListFlip, eFlip;
  ListRecCompFacet:=[];
  ListStatus:=[];
  FuncInsert:=function(eRecCompFacet)
    local iRec, test;
    for iRec in [1..Length(ListRecCompFacet)]
    do
      test:=VOR_L1_TestEquivalenceCompFacet(eRecL1, eRecCompFacet, ListRecCompFacet[iRec]);
      if test<>false then
        return;
      fi;
    od;
    Add(ListRecCompFacet, eRecCompFacet);
    Add(ListStatus, 0);
    Print("Now |ListRecCompFacet|=", Length(ListRecCompFacet), "\n");
  end;
  FuncInsert(VOR_L1_GetInitialComponent(eRecL1));
  Print("We have initial component\n");
  while(true)
  do
    IsFinished:=true;
    nbRec:=Length(ListRecCompFacet);
    for iRec in [1..nbRec]
    do
      if ListStatus[iRec]=0 then
        ListStatus[iRec]:=1;
        ListFlip:=VOR_L1_GetAllFlips(eRecL1, ListRecCompFacet[iRec]);
        for eFlip in ListFlip
        do
          FuncInsert(eFlip);
        od;
        IsFinished:=false;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  return ListRecCompFacet;
end;


VOR_L1_GetCellNeighbors:=function(eRecL1, eRecCompCell)
  local n, eRecIneq, ListIneqIrred, eRecStab, EXTred, EXText, FACrel, ListInc, O, ListFlip, minSizeClos, eO, eInc, soughtDimLin, ComputeAdjacencyFamily, EXTtot, FACtot, NewRecCompCell, iO, nbO;
  n:=eRecL1.n;
  eRecIneq:=VOR_L1_GetInequalities(eRecL1, eRecCompCell);
  ListIneqIrred:=RemoveRedundancyByDualDescription(eRecIneq.ListIneqRed);
  eRecStab:=VOR_L1_AutomorphismCompFacet(eRecL1, eRecCompCell);
  EXTred:=eRecStab.EXTred;
  EXText:=List(eRecStab.EXT, x->Concatenation([1], x));
  FACrel:=DualDescription(EXText);
  ListInc:=List(ListIneqIrred, x->Filtered([1..Length(EXTred)], y->x*EXTred[y]=0));
  ListFlip:=[];
  minSizeClos:=1;
  soughtDimLin:=n;
  ComputeAdjacencyFamily:=function(eO)
    local eInc, EXTinc, EXTfac, eRecProj, eSelect, EXTfacProj, FACfacProj, TotVol, eIso, RecStabComp, ListGenMatrProj, eGen, ePerm, eGenMatProj, GRPmatProj, eIneq, eIneqRed, eDir, SumVol, ListEXT, ListFAC, RecOrb, IsCorrect, GetOneRandomPoint, FindOneNeighbor, eMat, TheVol, eCentProj, TestPairwiseIntersection, TestInclusionInBig, eDen, iter, Nb;
    eInc:=eO[1];
    EXTinc:=eRecStab.EXT{eInc};
    EXTfac:=EXText{eInc};
    eRecProj:=ColumnReductionExten(EXTfac);
    eSelect:=eRecProj.Select;
    EXTfacProj:=eRecProj.EXT;
    FACfacProj:=List(DualDescription(EXTfacProj), RemoveFraction);
    TotVol:=VolumeComputationPolytope(EXTfacProj);
    eIso:=Isobarycenter(EXTinc);
    RecStabComp:=VOR_L1_AutomorphismPoint(eRecL1, eIso);
    ListGenMatrProj:=[];
    for eGen in GeneratorsOfGroup(RecStabComp.GRPaff)
    do
      ePerm:=PermList(List(EXTfac, x->Position(EXTfac, x*eGen)));
      eGenMatProj:=FindTransformation(EXTfacProj, EXTfacProj, ePerm);
      Add(ListGenMatrProj, eGenMatProj);
    od;
    GRPmatProj:=Group(ListGenMatrProj);
    eIneq:=__FindFacetInequality(EXText, eInc);
    eIneqRed:=eIneq{[2..n+1]};
    eDir:=-eIneqRed*Inverse(eRecL1.GramMat);
    eDen:=1;
    #
    TestInclusionInBig:=function()
      local EXT, eEXT;
      for EXT in ListEXT
      do
        for eEXT in EXT
        do
          if First(FACfacProj, x->x*eEXT<0)<>fail then
            Error("Problem in inclusion in big polytope");
          fi;
        od;
      od;
    end;
    TestPairwiseIntersection:=function()
      local ePair, eFAC, fFAC, FACtot, LinSp;
      for ePair in Combinations(ListFAC,2)
      do
        eFAC:=ePair[1];
        fFAC:=ePair[2];
        FACtot:=Concatenation(eFAC, fFAC);
        LinSp:=LinearDeterminedByInequalities(FACtot);
        if Length(LinSp)=n then
          Error("Non-trivial intersection");
        fi;
      od;
    end;
    SumVol:=0;
    ListEXT:=[];
    ListFAC:=[];
    IsCorrect:=function(ePoint)
      local ePointExt, ePointRed, FAC, test;
      ePointExt:=Concatenation([1], ePoint);
      ePointRed:=ePointExt{eSelect};
      if First(FACfacProj, x->x*ePointRed<=0)<>fail then
        return false;
      fi;
      for FAC in ListFAC
      do
        test:=First(FAC, x->x*ePointRed<0);
        if test=fail then
          return false;
        fi;
      od;
      return true;
    end;
    GetOneRandomPoint:=function()
      local N, ePointSum, eSum, eEXT, eVal, ePointRed, ePointExt, ePoint, nbAttempt, ePointApprox;
      N:=3;
      nbAttempt:=0;
      while(true)
      do
        ePointSum:=ListWithIdenticalEntries(Length(eSelect),0);
        eSum:=0;
        for eEXT in EXTfacProj
        do
          eVal:=Random([1..N]);
          eSum:=eSum + eVal;
          ePointSum:=ePointSum + eVal*eEXT;
        od;
        ePointRed:=ePointSum/eSum;
        ePointExt:=ePointRed*eRecProj.eMatBack;
        ePoint:=ePointExt{[2..n+1]};
        if IsCorrect(ePoint)=true then
          Print("ePoint=", ePoint, "\n");
          while(true)
          do
            eDen:=eDen+1;
            ePointApprox:=ApproximationVector(ePoint, eDen);
            Print("ePointApprox=", ePointApprox, "\n");
            if IsCorrect(ePointApprox)=true then
              return ePointApprox;
            fi;
          od;
        fi;
        N:=N+1;
        nbAttempt:=nbAttempt+1;
        Print("nbAttempt=", nbAttempt, "\n");
      od;
    end;
    FindOneNeighbor:=function()
      local h, ePointFAC, ePoint, ListViolated, eRecAnswer, NewCompCell, NewRecEXT, NewEXText, TheIncd, EXTneigh, EXTneighSel, FACneighSel, PreFACtot, FACtot, PreEXTtot, EXTtot, rnk, TheLin;
      h:=1/4;
      ePointFAC:=Isobarycenter(EXTinc);
      if IsCorrect(ePointFAC)=false then
        ePointFAC:=GetOneRandomPoint();
      fi;
      while(true)
      do
        ePoint:=ePointFAC + h*eDir;
        ListViolated:=Filtered(FACrel, x->x*Concatenation([1], ePoint)<0);
        Print("|ListViolated|=", Length(ListViolated), "\n");
        if Length(ListViolated)=1 then
          eRecAnswer:=VOR_L1_GetComponentFromPoint(eRecL1, ePoint, minSizeClos, soughtDimLin);
          if eRecAnswer.Answer=true then
            eDen:=1;
            NewCompCell:=eRecAnswer.eRecCompFacet;
            NewRecEXT:=VOR_L1_GetVertices(eRecL1, NewCompCell);
            NewEXText:=List(NewRecEXT.EXT, x->Concatenation([1], x));
            TheIncd:=Filtered(NewEXText, x->x*eIneq=0);
            rnk:=PersoRankMat(TheIncd);
            Print("rnk=", rnk, " n=", n, "\n");
            if rnk=n then
              EXTneigh:=Filtered(NewEXText, x->x*eIneq=0);
              EXTneighSel:=List(EXTneigh, x->x{eSelect});
              FACneighSel:=DualDescription(EXTneighSel);
              PreFACtot:=List(RemoveRedundancy(Concatenation(FACneighSel, FACfacProj)), RemoveFraction);
              TheLin:=LinearDeterminedByInequalities(PreFACtot);
              if Length(TheLin)=n then
                PreEXTtot:=DualDescription(PreFACtot);
                FACtot:=Difference(Set(PreFACtot), Set(FACfacProj));
                EXTtot:=Set(List(PreEXTtot, x->x/x[1]));
                eRecAnswer.eRecCompFacet.NewEXText:=NewEXText;
                eRecAnswer.eRecCompFacet.EXTtot:=EXTtot;
                eRecAnswer.eRecCompFacet.FACtot:=FACtot;
                if Position(ListEXT, EXTtot)=fail then
                  break;
                fi;
              fi;
            fi;
          fi;
          if eRecAnswer.Answer=false and eRecAnswer.reason="eSet cause splitting" then
            Print("Update point\n");
            ePointFAC:=GetOneRandomPoint();
            h:=1/4;
          fi;
          if eRecAnswer.Answer=false and eRecAnswer.reason="Too large eSet inducing artificial space splitting" then
            Print("Update point\n");
            ePointFAC:=GetOneRandomPoint();
            h:=1/4;
          fi;
        fi;
        h:=h/2;
        Print("Now h=", h, "\n");
        if h< 1/10000 then
          Print("Debug from that point your problems\n");
          Print(NullMat(4));
        fi;
        Print("ePointFAC=", ePointFAC, "\n");
      od;
      Print("Exiting here\n");
      return eRecAnswer.eRecCompFacet;
    end;
    while(true)
    do
      NewRecCompCell:=FindOneNeighbor();
      Nb:=VOR_L1_GetNumberCheck();
      for iter in [1..Nb]
      do
        Print("iter=", iter, " / ", Nb, "\n");
        VOR_L1_TestConsistencySingleCell(eRecL1, NewRecCompCell);
      od;
      EXTtot:=NewRecCompCell.EXTtot;
      FACtot:=NewRecCompCell.FACtot;
      Add(ListFlip, NewRecCompCell);
      eCentProj:=Isobarycenter(EXTtot);
#      eCentExt:=eCentProj*eRecProj.eMatBack;
#      eCent:=eCentExt{[2..n+1]};
      TheVol:=VolumeComputationPolytope(EXTtot);
      RecOrb:=OrbitWithAction(GRPmatProj, eCentProj, OnPoints);
      SumVol:=SumVol + Length(RecOrb.ListCoset)*TheVol;
      if SumVol=TotVol then
        break;
      fi;
      for eMat in RecOrb.ListElement
      do
        Add(ListEXT, Set(EXTtot*eMat));
        Add(ListFAC, Set(FACtot*CongrMap(eMat)));
      od;
      if SumVol > TotVol then
        Error("Volume contradiction");
      fi;
    od;
  end;
  O:=Orbits(eRecStab.GRPext, ListInc, OnSets);
  nbO:=Length(O);
  for iO in [1..nbO]
  do
    Print("iO=", iO, " / ", nbO, "\n");
    eO:=O[iO];
    ComputeAdjacencyFamily(eO);
  od;
  return ListFlip;
end;

VOR_L1_FullEnumerationCell:=function(eRecL1)
  local ListRecCompCell, ListStatus, FuncInsert, IsFinished, nbRec, iRec, ListFlip, eFlip, Nb;
  VOR_L1_TestCorrectnessRecL1(eRecL1);
  eRecL1.ListHyperplane:=VOR_L1_GetHyperplanes(eRecL1);
  ListRecCompCell:=[];
  ListStatus:=[];
  FuncInsert:=function(eRecCompCell)
    local iRec, test, iter;
    for iRec in [1..Length(ListRecCompCell)]
    do
      test:=VOR_L1_TestEquivalenceCompFacet(eRecL1, eRecCompCell, ListRecCompCell[iRec]);
      if test<>false then
        return;
      fi;
    od;
    Nb:=VOR_L1_GetNumberCheck();
    for iter in [1..Nb]
    do
      Print("iter=", iter, " / ", Nb, "\n");
      VOR_L1_TestConsistencySingleCell(eRecL1, eRecCompCell);
    od;
    Add(ListRecCompCell, eRecCompCell);
    Add(ListStatus, 0);
    Print("Now |ListRecCompCell|=", Length(ListRecCompCell), "\n");
  end;
  FuncInsert(VOR_L1_GetInitialCell(eRecL1));
  Print("We have initial component\n");
  while(true)
  do
    IsFinished:=true;
    nbRec:=Length(ListRecCompCell);
    for iRec in [1..nbRec]
    do
      if ListStatus[iRec]=0 then
        ListStatus[iRec]:=1;
        ListFlip:=VOR_L1_GetCellNeighbors(eRecL1, ListRecCompCell[iRec]);
        for eFlip in ListFlip
        do
          FuncInsert(eFlip);
        od;
        IsFinished:=false;
      fi;
    od;
    if IsFinished then
      break;
    fi;
  od;
  return ListRecCompCell;
end;


VOR_L1_FullEnumerationFacet:=function(eRecL1, ListRecCompCell)
  local ListEXTinc, FuncInsert, eRecCompCell, eRecStab, Lorb, eOrb, EXTinc, nbOrb, iOrb, eVectInt;
  ListEXTinc:=[];
  FuncInsert:=function(NewEXTinc)
    local eEXTinc, test;
    for eEXTinc in ListEXTinc
    do
      test:=VOR_L1_TestEquivalenceVertices(eRecL1, Isobarycenter(NewEXTinc), Isobarycenter(eEXTinc));
      if test<>false then
        return;
      fi;
    od;
    Add(ListEXTinc, NewEXTinc);
  end;
  for eRecCompCell in ListRecCompCell
  do
    eRecStab:=VOR_L1_AutomorphismCompFacet(eRecL1, eRecCompCell);
    Lorb:=DualDescriptionStandard(eRecStab.EXText, eRecStab.GRPext);
    eVectInt:=First(eRecStab.EXT, IsIntegralVector);
    if eVectInt<>fail then
      nbOrb:=Length(Lorb);
      for iOrb in [1..nbOrb]
      do
        Print("iOrb=", iOrb, " / ", nbOrb, "\n");
        eOrb:=Lorb[iOrb];
        EXTinc:=List(eRecStab.EXT{eOrb}, x->x-eVectInt);
        if First(EXTinc, IsIntegralVector)=fail then
          FuncInsert(EXTinc);
        fi;
      od;
    fi;
  od;
  return ListEXTinc;
end;


VOR_L1_GetContainingVertices:=function(eRecL1, ListRecCompFacet)
  local GRP, ListVerticesVoronoi, FuncInsert, eRecCompFacet, eRecEXT, eEqui, eEXT, eDiff, ListPermGens, eList, GRPperm, eSet, FuncInsertFacet, ListFacetOrbit, eGen, ListOrbitSize, ListOrbitRepr, Overt, eO, ListOrbitEquiSize;
  GRP:=eRecL1.PointGRP;
  ListVerticesVoronoi:=[];
  FuncInsert:=function(eVert)
    local O;
    if eVert in ListVerticesVoronoi then
      return;
    fi;
    O:=Orbit(GRP, eVert, OnPoints);
    Append(ListVerticesVoronoi, O);
  end;
  for eRecCompFacet in ListRecCompFacet
  do
    eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompFacet);
    for eEqui in eRecCompFacet.ListEqui
    do
      for eEXT in eRecEXT.EXT
      do
        eDiff:=eEXT - eEqui.ePt;
        FuncInsert(eDiff);
      od;
    od;
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List(ListVerticesVoronoi, x->Position(ListVerticesVoronoi, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  GRPperm:=Group(ListPermGens);
  ListFacetOrbit:=[];
  ListOrbitEquiSize:=[];
  FuncInsertFacet:=function(eSet)
    local fSet, test, eStab, OrbSize;
    for fSet in ListFacetOrbit
    do
      test:=RepresentativeAction(GRPperm, eSet, fSet, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    Add(ListFacetOrbit, eSet);
    eStab:=Stabilizer(GRPperm, eSet, OnSets);
    OrbSize:=Order(GRPperm)/Order(eStab);
    Add(ListOrbitEquiSize, OrbSize);
  end;
  for eRecCompFacet in ListRecCompFacet
  do
    eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompFacet);
    for eEqui in eRecCompFacet.ListEqui
    do
      eList:=[];
      for eEXT in eRecEXT.EXT
      do
        eDiff:=eEXT - eEqui.ePt;
        Add(eList, Position(ListVerticesVoronoi, eDiff));
      od;
      eSet:=Set(eList);
      FuncInsertFacet(eSet);
    od;
  od;
  Overt:=Orbits(GRPperm, [1..Length(ListVerticesVoronoi)], OnPoints);
  ListOrbitSize:=[];
  ListOrbitRepr:=[];
  for eO in Overt
  do
    Add(ListOrbitSize, Length(eO));
    Add(ListOrbitRepr, ListVerticesVoronoi[eO[1]]);
  od;
  return rec(ListVerticesVoronoi:=ListVerticesVoronoi, 
             GRPperm:=GRPperm, 
             ListOrbitSize:=ListOrbitSize, 
             ListOrbitRepr:=ListOrbitRepr, 
             ListOrbitEquiSize:=ListOrbitEquiSize, 
             ListFacetOrbit:=ListFacetOrbit);
end;



TestConsistencyListCompCell:=function(eRecL1, ListRecCompCell, Nb)
  local eRecCompCell, iter;
  for eRecCompCell in ListRecCompCell
  do
    for iter in [1..Nb]
    do
      Print("iter=", iter, " / ", Nb, "\n");
      VOR_L1_TestConsistencySingleCell(eRecL1, eRecCompCell);
    od;
  od;
end;




SearchPairwiseIntersection:=function(eRecL1, ListEXT)
  local n, TheAct, TotalListEXT, TotalListFAC, EXT, eCent, FAC, eCentRed, eRecOrb, eElt, EXTimg, eCentImg, eCentImgRed, eTrans, eMatB, eEltB, nbCell, ePair, iCell, jCell;
  n:=eRecL1.n;
  TheAct:=function(x, g)
    return PeriodicVectorMod1(x*g);
  end;
  TotalListEXT:=[];
  TotalListFAC:=[];
  for EXT in ListEXT
  do
    eCent:=Isobarycenter(EXT);
    FAC:=DualDescription(EXT);
    eCentRed:=PeriodicVectorMod1(eCent);
    eRecOrb:=OrbitWithAction(eRecL1.GRPaff, eCentRed, TheAct);
    for eElt in eRecOrb.ListElement
    do
      EXTimg:=EXT*eElt;
      eCentImg:=Isobarycenter(EXTimg);
      eCentImgRed:=PeriodicVectorMod1(eCentImg);
      eTrans:=eCentImgRed{[2..n+1]} - eCentImg{[2..n+1]};
      eMatB:=FuncCreateBigMatrix(eTrans, IdentityMat(n));
      eEltB:=eElt*eMatB;
      Add(TotalListEXT, Set(EXT*eEltB));
      Add(TotalListFAC, Set(FAC*CongrMap(eEltB)));
    od;
  od;
  nbCell:=Length(TotalListEXT);
  for ePair in Combinations([1..nbCell], 2)
  do
    iCell:=ePair[1];
    jCell:=ePair[2];
  od;

end;


PrintListRecCompFacet:=function(output, eRecL1, ListRecCompFacet, eRecVoronoi)
  local EXTnice, iOrb, nbOrb, EXTequi;
  EXTnice:=eRecVoronoi.ListVerticesVoronoi*eRecL1.ListVect;
  AppendTo(output, "List of Voronoi vertices\n");
  WriteMatrix(output, EXTnice);
  nbOrb:=Length(eRecVoronoi.ListOrbitSize);
  AppendTo(output, "Representatives of orbits of vertices\n");
  for iOrb in [1..nbOrb]
  do
    AppendTo(output, iOrb, "/", nbOrb, " |O|=", eRecVoronoi.ListOrbitSize[iOrb], " eRepr=");
    WriteVector(output, eRecVoronoi.ListOrbitRepr[iOrb]*eRecL1.ListVect);
  od;
  AppendTo(output, "Representatives of orbits of Equi planes\n");
  nbOrb:=Length(eRecVoronoi.ListFacetOrbit);
  for iOrb in [1..nbOrb]
  do
    AppendTo(output, iOrb, "/", nbOrb, " |O|=", eRecVoronoi.ListOrbitEquiSize[iOrb], " eRepr=\n");
    EXTequi:=eRecVoronoi.ListVerticesVoronoi{eRecVoronoi.ListFacetOrbit[iOrb]};
    WriteMatrix(output, EXTequi);
  od;
end;

VOR_L1_GetOrbitVertexVoronoi:=function(eRecL1, ListRecCompCell)
  local GRP, ListVerticesVoronoi, FuncInsert, eRecCompCell, eRecEXT, ListInt, ListNonInt, eEXT, fEXT, eDiff, ListPermGens, eGen, eList, GRPperm, Overt, ListOrbitSize, ListOrbitRepr, eO;
  GRP:=eRecL1.PointGRP;
  ListVerticesVoronoi:=[];
  FuncInsert:=function(eVert)
    local O;
    if eVert in ListVerticesVoronoi then
      return;
    fi;
    O:=Orbit(GRP, eVert, OnPoints);
    Append(ListVerticesVoronoi, O);
  end;
  for eRecCompCell in ListRecCompCell
  do
    eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompCell);
    ListInt:=Filtered(eRecEXT.EXT, IsIntegralVector);
    ListNonInt:=Filtered(eRecEXT.EXT, x->IsIntegralVector(x)=false);
    for eEXT in ListInt
    do
      for fEXT in ListNonInt
      do
        eDiff:=fEXT - eEXT;
        FuncInsert(eDiff);
      od;
    od;
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List(ListVerticesVoronoi, x->Position(ListVerticesVoronoi, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  GRPperm:=Group(ListPermGens);
  Overt:=Orbits(GRPperm, [1..Length(ListVerticesVoronoi)], OnPoints);
  ListOrbitSize:=[];
  ListOrbitRepr:=[];
  for eO in Overt
  do
    Add(ListOrbitSize, Length(eO));
    Add(ListOrbitRepr, ListVerticesVoronoi[eO[1]]);
  od;
  return rec(ListVerticesVoronoi:=ListVerticesVoronoi, 
             GRPperm:=GRPperm, 
             ListOrbitSize:=ListOrbitSize, 
             ListOrbitRepr:=ListOrbitRepr);
end;


VOR_L1_Get_Dvertices:=function(eRecL1, ListRecCompCell)
  local ListVertices, FuncInsert, ListNbMax, eRecCompCell, eRecEXT, eEqui, hVect, ListVal, MaxVal, nbMax, i, eVal, IsMax, ListDvertices, FAC, IsTrueVertex, eVert1, eVert2, eRefPt, ListSets, ListIncd, ListFacSets, iRecCompCell, n, ListEXText, EXText, ListListJRec, ListJRec, jRec, ListTrueDim, ListTrueNbMax, eList, eSet;
  ListVertices:=[];
  n:=eRecL1.n;
  FuncInsert:=function(eVert1, eVert2, eRecEXT, iRecCompCell, ListFacSets, eVal, IsMax)
    local nbRec, iRec, fRecVert, test, eRec, FuncInsertFacSet, eFacSet, ListEntFac, eVert3, GRPaff, FuncInsertFAC, FuncInsertBlock, eIsoExt, eIso;
    nbRec:=Length(ListVertices);
    eVert3:=(eVert1 + 2*eVert2)/3;
    FuncInsertFAC:=function(EXT, eFAC, iRec)
      local len, eIsoFAC, iEnt, test, eFACimg, EXTimg, eRecOrb, fBigMat, EXTimgB, eStab, ListEXT;
      len:=Length(ListVertices[iRec].ListEntIso);
      eIsoFAC:=Isobarycenter(eFAC);
      for iEnt in [1..len]
      do
        test:=RepresentativeAction(ListVertices[iRec].GRPaff, eIsoFAC, ListVertices[iRec].ListEntIso[iEnt].eIsoFAC, OnPoints);
        if test<>fail then
          eFACimg:=Set(eFAC*test);
          if eFACimg<>ListVertices[iRec].ListEntIso[iEnt].eFAC then
            Error("equivalence error");
          fi;
          EXTimg:=EXT*test;
          eRecOrb:=OrbitWithAction(ListVertices[iRec].ListEntIso[iEnt].eStab, Isobarycenter(EXTimg), OnPoints);
#          Print("1: |ListElement|=", Length(eRecOrb.ListElement), "\n");
          for fBigMat in eRecOrb.ListElement
          do
            EXTimgB:=Set(EXTimg*fBigMat);
            AddSet(ListVertices[iRec].ListEntIso[iEnt].ListEXT, EXTimgB);
          od;
          return;
        fi;
      od;
      eStab:=Stabilizer(ListVertices[iRec].GRPaff, eIsoFAC, OnPoints);
      eRecOrb:=OrbitWithAction(eStab, Isobarycenter(EXT), OnPoints);
#      Print("2: |ListElement|=", Length(eRecOrb.ListElement), "\n");
      ListEXT:=[];
      for fBigMat in eRecOrb.ListElement
      do
        EXTimgB:=Set(EXT*fBigMat);
        AddSet(ListEXT, EXTimgB);
      od;
      Add(ListVertices[iRec].ListEntIso, rec(eIsoFAC:=eIsoFAC, eFAC:=eFAC, eStab:=eStab, ListEXT:=ListEXT));
    end;
    FuncInsertBlock:=function(EXText, ListFacSets, eBigMat, iRec)
      local EXTimg, eFacSet, fFacSet;
      EXTimg:=EXText*eBigMat;
      for eFacSet in ListFacSets
      do
        fFacSet:=Set(eFacSet*eBigMat);
        FuncInsertFAC(EXTimg, fFacSet, iRec);
      od;
    end;
    for iRec in [1..nbRec]
    do
      fRecVert:=ListVertices[iRec];
      test:=VOR_L1_TestEquivalenceVertices(eRecL1, eVert3, fRecVert.eVert3);
#      Print("eVert3=", eVert3, " fRecVert.eVert3=", fRecVert.eVert3, " test=", test, "\n");
      if test<>false then
        if eVert1*test.eElt + test.eTrans <>fRecVert.eVert1 then
          Error("Equiv error 1");
        fi;
        if eVert2*test.eElt + test.eTrans <>fRecVert.eVert2 then
          Error("Equiv error 2");
        fi;
        if eVert3*test.eElt + test.eTrans <>fRecVert.eVert3 then
          Error("Equiv error 3");
        fi;
        if fRecVert.eVal<>eVal then
          Error("Inconsistent with norm continuity");
        fi;
        if IsMax=false then
          ListVertices[iRec].IsMax:=false;
        fi;
        FuncInsertBlock(eRecEXT.EXText, ListFacSets, test.eBigMat, iRec);
        return;
      fi;
    od;
    GRPaff:=VOR_L1_AutomorphismPoint(eRecL1, eVert3).GRPaff;
    eRec:=rec(eVert1:=eVert1, eVert2:=eVert2, eVert3:=eVert3, eReceXT:=eRecEXT, iRecCompCell:=iRecCompCell, eVal:=eVal, IsMax:=IsMax, ListEntIso:=[], GRPaff:=GRPaff);
    Add(ListVertices, eRec);
    FuncInsertBlock(eRecEXT.EXText, ListFacSets, IdentityMat(n+1), Length(ListVertices));
  end;
  ListNbMax:=[];
  ListEXText:=[];
  ListListJRec:=[];
  for iRecCompCell in [1..Length(ListRecCompCell)]
  do
    eRecCompCell:=ListRecCompCell[iRecCompCell];
    eRecEXT:=VOR_L1_GetVertices(eRecL1, eRecCompCell);
    EXText:=eRecEXT.EXText;
    ListSets:=DualDescriptionSets(EXText);
    Add(ListEXText, EXText);
    eEqui:=eRecCompCell.ListEqui[1];
    hVect:=eRecL1.MatrixVector[eEqui.posIneq];
    if Length(eRecCompCell.ListEqui)<>1 then
      Error("This is quite clearly a bug, ListEqui should be 1 element");
    fi;
    eRefPt:=eEqui.ePt;
    ListVal:=List(eRecEXT.EXT, x->(x - eRefPt)*hVect);
    MaxVal:=Maximum(ListVal);
    nbMax:=0;
    ListJRec:=[];
    for i in [1..Length(eRecEXT.EXT)]
    do
      eVal:=ListVal[i];
      IsMax:=eVal=MaxVal;
      if IsMax then
        nbMax:=nbMax+1;
      fi;
      ListIncd:=Filtered(ListSets, x->Position(x, i)<>fail);
      ListFacSets:=List(ListIncd, x->Set(eRecEXT.EXText{x}));
      eVert1:=eRefPt;
      eVert2:=eRecEXT.EXT[i];
      jRec:=FuncInsert(eVert1, eVert2, eRecEXT, iRecCompCell, ListFacSets, eVal, IsMax);
      Add(ListJRec, jRec);
    od;
    Add(ListListJRec, ListJRec);
    Add(ListNbMax, nbMax);
  od;
  ListTrueNbMax:=[];
  ListTrueDim:=[];
  for iRecCompCell in [1..Length(ListRecCompCell)]
  do
    eList:=ListListJRec[iRecCompCell];
    eSet:=Filtered([1..Length(eList)], x->ListVertices[eList[x]].IsMax=true);
    Add(ListTrueNbMax, Length(eSet));
    Add(ListTrueDim, PersoRankMat(ListEXText[iRecCompCell]{eSet}));
  od;
  IsTrueVertex:=function(eRecVertex)
    local ListPlane, eEntIso, EXT, NSP, nbContEXT, eIso, eRecOrb, fBigMat, eFACimg;
    ListPlane:=[];
    for eEntIso in eRecVertex.ListEntIso
    do
      nbContEXT:=Length(Set(eEntIso.ListEXT));
      if nbContEXT<>1 and nbContEXT<>2 then
        Error("Another polyhedral error");
      fi;
      if nbContEXT=1 then
        eIso:=Isobarycenter(eEntIso.eFAC);
        eRecOrb:=OrbitWithAction(eRecVertex.GRPaff, eIso, OnPoints);
        for fBigMat in eRecOrb.ListElement
        do
          eFACimg:=eEntIso.eFAC*fBigMat;
          NSP:=NullspaceMat(TransposedMat(eFACimg));
          if Length(NSP)<>1 then
            Error("Another polyhedral error 2");
          fi;
          Add(ListPlane, NSP[1]);
        od;
      fi;
    od;
    if PersoRankMat(ListPlane)=eRecL1.n then
      return true;
    fi;
    return false;
  end;
  for i in [1..Length(ListVertices)]
  do
    ListVertices[i].IsTrueVertex:=IsTrueVertex(ListVertices[i]);
  od;
  return rec(ListVertices:=ListVertices, ListNbMax:=ListNbMax, ListTrueNbMax:=ListTrueNbMax, ListTrueDim:=ListTrueDim, LocalMaxDim:=Maximum(ListTrueDim)-1);
end;

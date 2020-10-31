FileGetDate:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"GetDate");
FileRatToString:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"RatToString");



InstallGlobalFunction(PrevIdx,
function(NBU, idx)
  if idx=1 then
    return NBU;
  else
    return idx-1;
  fi;
end);



InstallGlobalFunction(NextIdx,
function(NBU, idx)
  if idx=NBU then
    return 1;
  else
    return idx+1;
  fi;
end);


#
# k must be smaller than NBU
InstallGlobalFunction(NextKIdx,
function(NBU, idx, k)
  if idx<=NBU-k then
    return idx+k;
  else
    return idx+k-NBU;
  fi;
end);



InstallGlobalFunction(PrevKIdx,
function(NBU, idx, k)
  if idx>=k+1 then
    return idx-k;
  else
    return idx+NBU-k;
  fi;
end);



InstallGlobalFunction(PersoGroupPerm,
function(ListGen)
  if Length(ListGen)=0 then
    return Group(());
  else
    return Group(ListGen);
  fi;
end);



InstallGlobalFunction(BinomialStdvect_Increment,
function(n, k, eVect)
  local retVect, i, xy2, test;
  retVect:=[];
  for i in [1..k]
  do
    retVect[i]:=eVect[i];
  od;
  retVect[1]:=retVect[1]+1;
  xy2:=2;
  while(true)
  do
    if (xy2 <= k) and (retVect[xy2-1] >= retVect[xy2]) then
      retVect[xy2]:=retVect[xy2]+1;
      xy2:=xy2+1;
    else
      break;
    fi;
  od;
  if (xy2 > 2) then
    for i in [1..xy2-2]
    do
      retVect[i]:=i;
    od;
  fi;
  if retVect[k]>n then
    test:=false;
  else
    test:=true;
  fi;
  return rec(eVect:=retVect, test:=test);
end);


InstallGlobalFunction(IsRankOneMatrix,
function(SymMat)
  local eRec, n, ListP, ListM, fMat, eCoeff, eVal, pos, i, V;
  eRec:=RemoveFractionMatrixPlusCoef(SymMat);
  n:=Length(eRec.TheMat);
  if eRec.TheMat=NullMat(n,n) then
    return rec(result:=true, coeff:=0, V:=ListWithIdenticalEntries(n,0));
  fi;
  ListP:=Filtered([1..n], x->eRec.TheMat[x][x] > 0);
  ListM:=Filtered([1..n], x->eRec.TheMat[x][x] < 0);
  if Length(ListP)>0 and Length(ListM)>0 then
    Print("Case 1: false\n");
    return rec(result:=false);
  fi;
  if Length(ListP)=0 and Length(ListM)=0 then
    Print("Case 2: false\n");
    return rec(result:=false);
  fi;
  # making the diagonal positive
  if Length(ListP)>0 then
    fMat:=eRec.TheMat;
    eCoeff:=eRec.TheMult;
  else
    fMat:= - eRec.TheMat;
    eCoeff:= - eRec.TheMult;
  fi;
  # Testing rationality
  for i in [1..n]
  do
    eVal:=fMat[i][i];
    if IsInt(Sqrt(eVal))=false then
    Print("Case 3: false\n");
      return rec(result:=false);
    fi;
  od;
  pos:=First([1..n], x->fMat[x][x]>0);
  if pos=fail then
    Error("We have a bug to resolve 1");
  fi;
  V:=ListWithIdenticalEntries(n,0);
  V[pos]:=Sqrt(fMat[pos][pos]);
  for i in [1..n]
  do
    if i<>pos then
      V[i] := fMat[i][pos] / V[pos];
    fi;
  od;
  if fMat <> TransposedMat([V])*[V] then
    Print("Case 4: false\n");
    return rec(result:=false);
  fi;
  if SymMat <> eCoeff * TransposedMat([V])*[V] then
    Error("We have a bug to resolve 2");
  fi;
  return rec(result:=true, coeff:=eCoeff, V:=V);
end);



InstallGlobalFunction(PowerSet_Increment,
function(n, k, eVect)
  local retVect, i, FirstValue;
  retVect:=[];
  for i in [1..n]
  do
    retVect[i]:=eVect[i];
  od;
  FirstValue:=-1;
  for i in [1..n]
  do
    if FirstValue=-1 then
      if eVect[i]<k then
        FirstValue:=i;
      fi;
    fi;
  od;
  if FirstValue=-1 then
    return rec(eVect:=retVect, test:=false);
  fi;
  retVect[FirstValue]:=retVect[FirstValue]+1;
  for i in [1..FirstValue-1]
  do
    retVect[i]:=1;
  od;
  return rec(eVect:=retVect, test:=true);
end);



# this procedure Build the Set:  Seto x Seto x .... x Seto
InstallGlobalFunction(BuildSet,
function(n, Seto)
  local DO, i, iCol, U, V,C, eVal;
  DO:=[[]];
  for iCol in [1..n]
  do
    C:=ShallowCopy(DO);
    DO:=ShallowCopy([]);
    for i in [1..Length(C)]
    do
      for eVal in Seto
      do
        U:=ShallowCopy(C[i]);
        Add(U, eVal);
        Add(DO, U);
      od;
    od;
  od;
  return DO;
end);





InstallGlobalFunction(ExpressPairsAsCycle,
function(ListPair)
  local nbPair, ListStatus, ThePoint, RetList, jPair, iPair;
  nbPair:=Length(ListPair);
  ListStatus:=ListWithIdenticalEntries(nbPair,0);
  ThePoint:=ListPair[1][1];
  RetList:=[];
  for iPair in [1..nbPair]
  do
    Add(RetList, ThePoint);
    jPair:=First([1..nbPair], x->ListStatus[x]=0 and Position(ListPair[x],ThePoint)<>fail);
    if jPair=fail then
      Error("Debug here");
    fi;
    ThePoint:=Difference(Set(ListPair[jPair]),[ThePoint])[1];
    ListStatus[jPair]:=1;
  od;
  return RetList;
end);



InstallGlobalFunction(UndoCollected,
function(ListColl)
  local TheRet, eColl, i;
  TheRet:=[];
  for eColl in ListColl
  do
    for i in [1..eColl[2]]
    do
      Add(TheRet, eColl[1]);
    od;
  od;
  return TheRet;
end);




InstallGlobalFunction(GetMatrixCoset,
function(eMat)
  local eDet, TheDim, ListCoset, eMatBas, ListStatus, FuncInsert, IsFinished, nbCos, iCos, i, eNewVect;
  eDet:=AbsInt(DeterminantMat(eMat));
  TheDim:=Length(eMat);
  ListCoset:=[ListWithIdenticalEntries(TheDim,0)];
  eMatBas:=IdentityMat(TheDim);
  ListStatus:=[0];
  FuncInsert:=function(eNewVect)
    local eVect;
    for eVect in ListCoset
    do
      if SolutionIntMat(eMat, eVect-eNewVect)<>fail then
        return;
      fi;
    od;
    Add(ListCoset, eNewVect);
    Add(ListStatus, 0);
  end;
  while(true)
  do
    IsFinished:=true;
    nbCos:=Length(ListCoset);
    for iCos in [1..nbCos]
    do
      if ListStatus[iCos]=0 then
        IsFinished:=false;
        ListStatus[iCos]:=1;
        for i in [1..TheDim]
        do
          eNewVect:=ListCoset[iCos] + eMatBas[i];
          FuncInsert(eNewVect);
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  if eDet<>nbCos then
    Error("Error in coset determination");
  fi;
  return ListCoset;
end);



InstallGlobalFunction(BuildSetMultiple,
function(ListSeto)
  local DO, eSet, C, eC, eVal, U;
  DO:=[[]];
  for eSet in ListSeto
  do
    C:=ShallowCopy(DO);
    DO:=ShallowCopy([]);
    for eC in C
    do
      for eVal in eSet
      do
	U:=ShallowCopy(eC);
        Add(U, eVal);
        Add(DO, U);
      od;
    od;
  od;
  return DO;
end);



InstallGlobalFunction(SetSelect,
function(eList)
  local eReordPerm, ePermInv, eListReord, TheSet, TheSelect, len, i, eElt, iBis, ThePrev, eSet, TheListSets;
  eReordPerm:=SortingPerm(eList);
  ePermInv:=eReordPerm^(-1);
  eListReord:=Permuted(eList, eReordPerm);
  TheSet:=[];
  TheSelect:=[];
  TheListSets:=[];
  len:=Length(eList);
  eSet:=[];
  for i in [1..len]
  do
    eElt:=eListReord[i];
    iBis:=OnPoints(i, ePermInv);
    if i>1 then
      if ThePrev<>eElt then
        Add(TheSet, eElt);
        Add(TheSelect, iBis);
        ThePrev:=eElt;
        Add(TheListSets, eSet);
        eSet:=[iBis];
      else
        Add(eSet, iBis);
      fi;
    else
      ThePrev:=eElt;
      Add(TheSet, eElt);
      Add(TheSelect, iBis);
      eSet:=[iBis];
    fi;
  od;
  if Length(eSet)>0 then
    Add(TheListSets, eSet);
  fi;
  return rec(TheSet:=TheSet, TheSelect:=TheSelect, TheListSets:=TheListSets);
end);



InstallGlobalFunction(Isobarycenter,
function(EXT)
  return Sum(EXT)/Length(EXT);
end);



InstallGlobalFunction(AntipodalDecomposition,
function(EXT)
  local eIso, len, ListPair, i, eEXT, fEXT, j;
  eIso:=Isobarycenter(EXT);
  len:=Length(EXT);
  ListPair:=[];
  for i in [1..len]
  do
    eEXT:=EXT[i];
    fEXT:=2*eIso - eEXT;
    j:=Position(EXT, fEXT);
    if j>i then
      Add(ListPair, [i,j]);
    fi;
  od;
  return ListPair;
end);



InstallGlobalFunction(VectorMod1,
function(eVect)
  return List(eVect, FractionMod1);
end);



InstallGlobalFunction(PeriodicVectorMod1,
function(eVect)
  return Concatenation([1], List(eVect{[2..Length(eVect)]}, FractionMod1));
end);



InstallGlobalFunction(PeriodicOnClassesMod1,
function(x, eElt)
  return PeriodicVectorMod1(x*eElt);
end);



InstallGlobalFunction(OnClassesMod1,
function(eClass, eMat)
  return VectorMod1(eClass*eMat);
end);



InstallGlobalFunction(IsVectorRational,
function(eVect)
  local eX;
  for eX in eVect
  do
    if IsRat(eX)=false then
      return false;
    fi;
  od;
  return true;
end);



InstallGlobalFunction(IsMatrixRational,
function(eMat)
  local eVect;
  for eVect in eMat
  do
    if IsVectorRational(eVect)=false then
      return false;
    fi;
  od;
  return true;
end);





InstallGlobalFunction(GetCollectedList,
function(AppliSet, FCT)
  local RetListKeys, RetListOcc, ListKeys, ListOcc, RetListSizes, FuncInsert, i, eKey, pos, g, TheCollected;
  ListKeys:=[];
  ListOcc:=[];
  for i in [1..Length(AppliSet)]
  do
    eKey:=FCT(AppliSet[i]);
    pos:=Position(ListKeys, eKey);
    if pos=fail then
      Add(ListKeys, eKey);
      Add(ListOcc, [i]);
    else
      Add(ListOcc[pos], i);
    fi;
  od;
  g:=SortingPerm(ListKeys);
  RetListKeys:=Permuted(ListKeys, g);
  RetListOcc:=Permuted(ListOcc, g);
  RetListSizes:=List(RetListOcc, Length);
  TheCollected:=List([1..Length(ListKeys)], x->[RetListKeys[x], RetListSizes[x]]);
  return rec(ListKeys:=RetListKeys, ListOcc:=RetListOcc, ListSizes:=RetListSizes, TheCollected:=TheCollected);
end);



InstallGlobalFunction(TestConicness,
function(FAC)
  local eVal;
  for eVal in FAC
  do
    if eVal[1]<>0 then
      return false;
    fi;
  od;
  return true;
end);

InstallGlobalFunction(FacetOfInfinity,
function(n)
  local VZ;
  VZ:=ListWithIdenticalEntries(n, 0);
  VZ[1]:=1;
  return VZ;
end);

InstallGlobalFunction(IsIntegralVector,
function(eVect)
  local eVal;
  for eVal in eVect
  do
    if IsInt(eVal)=false then
      return false;
    fi;
  od;
  return true;
end);



InstallGlobalFunction(IsIntegralMat,
function(eMat)
  local eLine, eVal;
  for eLine in eMat
  do
    for eVal in eLine
    do
      if IsInt(eVal)=false then
        return false;
      fi;
    od;
  od;
  return true;
end);





InstallGlobalFunction(IsProportionalVector,
function(eVect1, eVect2)
  local n, eSet1, eSet2, eSetTest;
  n:=Length(eVect1);
  if n<>Length(eVect2) then
    Error("Vector should be of same length");
  fi;
  eSet1:=Filtered([1..n], x->eVect1[x]<>0);
  eSet2:=Filtered([1..n], x->eVect2[x]<>0);
  if eSet1<>eSet2 then
    return false;
  fi;
  eSetTest:=Set(List(eSet1, x->eVect1[x]/eVect2[x]));
  return Length(eSetTest)=1;
end);


InstallGlobalFunction(TestForRepetition,
function(ListVect)
  local i, j, nbVect, n, LIdx1, LIdx2, ListQuot;
  nbVect:=Length(ListVect);
  n:=Length(ListVect[1]);
  for i in [1..nbVect-1]
  do
    for j in [i+1..nbVect]
    do
      if Length(ListVect[i])<>Length(ListVect[j]) then
        Error("The vector have unequal lengths");
      fi;
      LIdx1:=Filtered([1..n], x->ListVect[i][x]<>0);
      LIdx2:=Filtered([1..n], x->ListVect[j][x]<>0);
      if LIdx1=LIdx2 then
        if Length(LIdx1)=0 then
          return true;
        fi;
        ListQuot:=Set(List(LIdx1, x->ListVect[i][x]/ListVect[j][x]));
        if Length(Set(ListQuot))=1 then
          return true;
        fi;
      fi;
    od;
  od;
  return false;
end);



InstallGlobalFunction(ZeroRankMat,
function(Mat);
  if Length(Mat)=0 then
    return 0;
  else
    return RankMat(Mat);
  fi;
end);



InstallGlobalFunction(ApproximationVector,
function(eVect, Lev)
  return List(Lev*eVect, NearestInteger)/Lev;
end);



InstallGlobalFunction(GetDate,
function()
  local FileD1, FileD2, reply;
  FileD1:=Filename(POLYHEDRAL_tmpdir,"DateFile1");
  FileD2:=Filename(POLYHEDRAL_tmpdir,"DateFile2");
  Exec("date +%s > ", FileD1);
  Exec(FileGetDate, " ", FileD1, " > ", FileD2);
  reply:=ReadAsFunction(FileD2)();
  RemoveFile(FileD1);
  RemoveFile(FileD2);
  return reply;
end);



InstallGlobalFunction(RandomSubset,
function(eSet, k)
  local i, sSet, V, h;
  sSet:=[];
  V:=ListWithIdenticalEntries(Length(eSet), 1);
  len:=0;
  while(true)
  do
    h:=Random([1..Length(eSet)]);
    if V[h]=1 then
      V[h]:=0;
      Add(sSet, eSet[h]);
      len:=len+1;
      if len=k then
          return Set(sSet);
      fi;
    fi;
  od;
end);



InstallGlobalFunction(WriteVector,
function(outputarg, eLine)
  local eVal;
  for eVal in eLine
  do
    WriteAll(outputarg, Concatenation(" ", String(eVal)));
  od;
  WriteAll(outputarg, "\n");
end);




InstallGlobalFunction(WriteMatrix,
function(outputarg, eMat)
  local eEXT;
  for eEXT in eMat
  do
    WriteVector(outputarg, eEXT);
  od;
end);



InstallGlobalFunction(CPP_WriteMatrix,
function(output, eMat)
  local nbRow, nbCol, iRow, iCol;
  nbRow:=Length(eMat);
  nbCol:=Length(eMat[1]);
  AppendTo(output, nbRow, " ", nbCol, "\n");
  for iRow in [1..nbRow]
  do
    for iCol in [1..nbCol]
    do
      AppendTo(output, " ", eMat[iRow][iCol]);
    od;
    AppendTo(output, "\n");
  od;
end);



InstallGlobalFunction(RowReduction,
function(arg)
  local MatrixWork, rankMatrixWork, PreSelect, Irr, rank, pos, TE, SelectSet;
  if IsBound(arg[4]) then
    Error("Too many argument to this function");
  elif IsBound(arg[3]) then
    MatrixWork:=arg[1];
    rankMatrixWork:=arg[2];
    PreSelect:=arg[3];
  elif IsBound(arg[2]) then
    MatrixWork:=arg[1];
    rankMatrixWork:=arg[2];
    PreSelect:=[];
  elif IsBound(arg[1]) then
    MatrixWork:=arg[1];
    rankMatrixWork:=RankMat(MatrixWork);
    PreSelect:=[];
  else
    Error("Please provide at least one argument");
  fi;
  if Length(PreSelect)>0 then
    if RankMat(MatrixWork{PreSelect}) < Length(PreSelect) then
      Error("your preselection will not work to the task");
    else
      SelectSet:=ShallowCopy(PreSelect);
      Irr:=MatrixWork{SelectSet};
      rank:=Length(PreSelect);
    fi;
  else
    Irr:=[];
    SelectSet:=[];
    rank:=0;
  fi;
  pos:=1;
  SelectSet:=[];
  while (rank<rankMatrixWork)
  do
    if Position(SelectSet, pos)=fail then
      TE:=ShallowCopy(Irr);
      Add(TE, MatrixWork[pos]);
      if (RankMat(TE) > rank) then
        Add(Irr, MatrixWork[pos]);
        Add(SelectSet, pos);
        rank:=rank+1;
      fi;
    fi;
    pos:=pos+1;
  od;
  return rec(EXT:=Irr, Select:=SelectSet);
end);



InstallGlobalFunction(ColumnReduction,
function(arg)
  local MatrixWork, rankMatrixWork, PreSelect, rep;
  if IsBound(arg[4]) then
    Error("Too many argument to this function");
  elif IsBound(arg[3]) then
    MatrixWork:=arg[1];
    rankMatrixWork:=arg[2];
    PreSelect:=arg[3];
  elif IsBound(arg[2]) then
    MatrixWork:=arg[1];
    rankMatrixWork:=arg[2];
    PreSelect:=[];
  elif IsBound(arg[1]) then
    MatrixWork:=arg[1];
    rankMatrixWork:=RankMat(MatrixWork);
    PreSelect:=[];
  else
    Error("Please provide at least one argument");
  fi;
  rep:=RowReduction(TransposedMat(MatrixWork), rankMatrixWork, PreSelect);
  return rec(EXT:=TransposedMat(rep.EXT), Select:=rep.Select);
end);



InstallGlobalFunction(ColumnReductionExten,
function(EXT)
  local eRec, eRecRow, EXTproj, EXTredProj, eMatBack, NSP;
  eRec:=ColumnReduction(EXT);
  eRecRow:=RowReduction(EXT);
  EXTproj:=EXT{eRecRow.Select};
  EXTredProj:=eRec.EXT{eRecRow.Select};
  eMatBack:=Inverse(EXTredProj)*EXTproj;
  NSP:=NullspaceMat(TransposedMat(EXT));
  return rec(EXT:=eRec.EXT, Select:=eRec.Select, eMatBack:=eMatBack, NSP:=NSP);
end);



InstallGlobalFunction(TranslateElement,
function(eElt, LSET, Action)
  local eList, iElt, Pos;
  eList:=[];
  for iElt in [1..Length(LSET)]
  do
    Pos:=Position(LSET, Action(LSET[iElt], eElt));
    if Pos=fail then
      Print("Translation of the group is impossible\n");
      return false;
    fi;
    Add(eList, Pos);
  od;
  return eList;
end);



InstallGlobalFunction(GcdVector,
function(TheVector)
  local eVal, TheVectorRed, LSred, LS1, ListCoef;
  if Length(TheVector)=1 then
    eVal:=TheVector[1];
    if eVal > 0 then
      return rec(TheGcd:=eVal, ListCoef:=[1]);
    fi;
    if eVal < 0 then
      return rec(TheGcd:=-eVal, ListCoef:=[-1]);
    fi;
    return rec(TheGcd:=0, ListCoef:=[1]);
  fi;
  TheVectorRed:=TheVector{[2..Length(TheVector)]};
  LSred:=GcdVector(TheVectorRed);
  LS1:=Gcdex(TheVector[1], LSred.TheGcd);
  ListCoef:=Concatenation([LS1.coeff1], LS1.coeff2*LSred.ListCoef);
  return rec(TheGcd:=LS1.gcd, ListCoef:=ListCoef);
end);



InstallGlobalFunction(GetZbasis,
function(ListElements)
  local TheDim, ListEqua, TheBasis, InvMatrix, eSet, GetOneBasis, ComputeSpeedingElements, FuncInsert, eElt, eEltRed, eSol, eLine, TheMult, DoCheck;
  if Length(ListElements)=0 then
    Print("|ListElements|=", Length(ListElements), "\n");
    Error("Problem in GetZbasis, we need at least one element");
  fi;
  TheDim:=Length(ListElements[1]);
  if RankMat(ListElements)=0 then
    return [];
  fi;
  ListEqua:=IdentityMat(TheDim);
  TheMult:=RemoveFractionMatrixPlusCoef(ListElements).TheMult;
  TheBasis:=[];
  InvMatrix:="irrelevant";
  eSet:=[];
  GetOneBasis:=function(eSol)
    local DimLoc, TheRedMat, eVect, iCol, n2, ListIdx, AbsList, TheMin, pos, ThePivot, r, q, NSP;
    DimLoc:=Length(TheBasis);
    TheRedMat:=Concatenation(IdentityMat(DimLoc), [eSol]);
    NSP:=NullspaceIntMat(RemoveFractionMatrix(TheRedMat));
    if Length(NSP)<>1 then
      Error("problem in computation of relation");
    fi;
    eVect:=ShallowCopy(NSP[1]);
    n2:=Length(eVect);
    while(true)
    do
      ListIdx:=Filtered([1..n2], x->eVect[x]<>0);
      if Length(ListIdx)=1 then
        return TheRedMat{Difference([1..n2], ListIdx)};
      fi;
      AbsList:=List(eVect{ListIdx}, AbsInt);
      TheMin:=Minimum(AbsList);
      pos:=Position(AbsList, TheMin);
      ThePivot:=ListIdx[pos];
      for iCol in Difference([1..n2], [ThePivot])
      do
        r:=eVect[iCol] mod AbsInt(eVect[ThePivot]);
        q:=(eVect[iCol] - r)/eVect[ThePivot];
        TheRedMat[ThePivot]:=TheRedMat[ThePivot]+q*TheRedMat[iCol];
        eVect[iCol]:=r;
        if First(eVect*TheRedMat, x->x<>0)<>fail then
          Error("inconsistency");
        fi;
      od;
    od;
  end;
  ComputeSpeedingElements:=function()
    ListEqua:=NullspaceMat(TransposedMat(TheBasis));
    eSet:=ColumnReduction(TheBasis).Select;
    InvMatrix:=Inverse(List(TheBasis, x->x{eSet}));
  end;
  FuncInsert:=function(eElt)
    local ListScal, TheSum, eEltRed, eSol, NewBasis, TheBasisNew;
    ListScal:=List(ListEqua, x->x*eElt);
    TheSum:=Sum(List(ListScal, x->x*x));
    if TheSum>0 then
      Add(TheBasis, eElt);
      TheBasis:=LLLReducedBasis(TheBasis).basis;
      ComputeSpeedingElements();
    else
      if Length(TheBasis)=0 then
        return;
      fi;
      eEltRed:=eElt{eSet};
      eSol:=eEltRed*InvMatrix;
      if IsIntegralVector(eSol) then
        return;
      fi;
      NewBasis:=GetOneBasis(eSol);
      TheBasisNew:=NewBasis*TheBasis;
      TheBasis:=LLLReducedBasis(TheBasisNew).basis;
      ComputeSpeedingElements();
    fi;
  end;
  for eElt in ListElements
  do
    FuncInsert(eElt);
  od;
  for eElt in ListElements
  do
    eEltRed:=eElt{eSet};
    eSol:=eEltRed*InvMatrix;
    if IsIntegralVector(eSol)=false then
      Error("Inconsistency in basis computation");
    fi;
  od;
  DoCheck:=true;
  if DoCheck then
    for eLine in TheBasis
    do
      eSol:=SolutionIntMat(ListElements*TheMult, eLine*TheMult);
      if eSol=fail then
        Error("Error in GetZbasis 1");
      fi;
    od;
    for eLine in ListElements
    do
      eSol:=SolutionIntMat(TheBasis*TheMult, eLine*TheMult);
      if eSol=fail then
        Error("Error in GetZbasis 2");
      fi;
    od;
  fi;
  return TheBasis;
end);



InstallGlobalFunction(TranslateGroup,
function(GRP, LSET, Action)
  if Order(GRP)=1 then
    return Group(());
  fi;
  return Group(List(GeneratorsOfGroup(GRP), x->PermList(TranslateElement(x, LSET, Action))));
end);



InstallGlobalFunction(TranslateGroupPlusHomomorphism,
function(GRP, LSET, Action)
  local LGen, GenNew, GrpNew, phi;
  if Order(GRP)=1 then
    return Group(());
  fi;
  LGen:=GeneratorsOfGroup(GRP);
  GenNew:=List(LGen, x->PermList(TranslateElement(x, LSET, Action)));
  GrpNew:=Group(GenNew);
  phi:=GroupHomomorphismByImagesNC(GRP, GrpNew, LGen, GenNew);
  return rec(GRP:=GrpNew, phi:=phi);
end);



#
#
# this procedure either returns false if the graph are not isomorphic or
# the list [.....] where the element in i-th position is the position of
# the i-th vertex of Graph1 in Graph2
InstallGlobalFunction(IsIsomorphicGraphDutourVersion,
function(Graph1, Graph2)
  local g1, g2, g;
  if IsIsomorphicGraph(Graph1, Graph2)=false then
    return false;
  else
    g1:=Graph1.canonicalLabelling;
    g2:=Graph2.canonicalLabelling;
    g:=g1^(-1)*g2;
    return List([1..Graph1.order], x->OnPoints(x, g));
  fi;
end);

#
#
# Select the element of Vect whose set of values belongs to ValueSet
InstallGlobalFunction(SelectValuedVect,
function(Vect, ValueSet)
  local Selected, eVect;
  Selected:=[];
  for eVect in Vect
  do
    if Length(Filtered(eVect, x->Position(ValueSet, x)=fail))=0 then
      Add(Selected, eVect);
    fi;
  od;
  return Selected;
end);



InstallGlobalFunction(FindTransformation,
function(ListVert1, ListVert2, eGen)
  local eMat1, eMat2, iVert, jVert, rnk, Irr1, Irr2, rank, pos, TE, TheMat, test1, test2;
  eMat1:=[];
  eMat2:=[];
  if Length(ListVert1)<>Length(ListVert2) then
    Error("Error in FindTransformation: vector length is not the same");
  fi;
  for iVert in [1..Length(ListVert1)]
  do
    Add(eMat1, ListVert1[iVert]);
    jVert:=OnPoints(iVert, eGen);
    Add(eMat2, ListVert2[jVert]);
  od;
  test1:=Set(List(ListVert1, x->x[1]))=[0];
  test2:=Set(List(ListVert2, x->x[1]))=[0];
  if test1<>test2 then
    Error("We have a mixup here in the nature of the cones");
  fi;
  if test1=true then
    Add(eMat1, FacetOfInfinity(Length(ListVert1[1])));
    Add(eMat2, FacetOfInfinity(Length(ListVert1[1])));
  fi;
  rnk:=RankMat(eMat2);
  if rnk<>Length(ListVert1[1]) then
    Error("Rank Error");
  fi;
  Irr1:=[];
  Irr2:=[];
  rank:=0;
  pos:=1;
  while (rank<rnk)
  do
    TE:=ShallowCopy(Irr1);
    Add(TE, eMat1[pos]);
    if (RankMat(TE) > rank) then
      Irr1:=ShallowCopy(TE);
      Add(Irr2, eMat2[pos]);
      rank:=rank+1;
    fi;
    pos:=pos+1;
  od;
  TheMat:=Inverse(Irr1)*Irr2;
  if eMat1*TheMat<>eMat2 then
    return fail;
  fi;
  return TheMat;
end);





#
#
# this procedure work with either all first coordinate equal to 0
# or all first coordinate equal to 1.
InstallGlobalFunction(TranslateToMatrixGroup,
function(EXT, GrpEXT)
  local Tconic, Dimension, FuncPermToMatrix, eGen, ListGeneratorMatrixGroup, MatrixElt;
  Tconic:=TestConicness(EXT);
  Print("Tconic=", Tconic, "\n");
  Dimension:=Length(EXT[1]);
  ListGeneratorMatrixGroup:=[];
  for eGen in GeneratorsOfGroup(GrpEXT)
  do
    MatrixElt:=FindTransformation(EXT, EXT, eGen);
    if MatrixElt=fail then
      return false;
    else
      Add(ListGeneratorMatrixGroup, MatrixElt);
    fi;
  od;
  if Length(ListGeneratorMatrixGroup)=0 then
    return Group([IdentityMat(Length(EXT))]);
  fi;
  return Group(ListGeneratorMatrixGroup);
end);



InstallGlobalFunction(SkeletonGraphDirect,
function(EXT, FAC)
  local Gra, DimAdj, iEXT, jEXT, Mat, eFac;
  Gra:=NullGraph(Group(()), Length(EXT));
  if TestConicness(FAC)=true then
    DimAdj:=Length(FAC[1])-3;
  else
    DimAdj:=Length(FAC[1])-2;
  fi;
  for iEXT in [1..Length(EXT)-1]
  do
    for jEXT in [iEXT+1..Length(EXT)]
    do
      Mat:=[];
      for eFac in FAC
      do
        if eFac*EXT[iEXT]=0 and eFac*EXT[jEXT]=0 then
          Add(Mat, eFac);
        fi;
      od;
      if DimAdj=ZeroRankMat(Mat) then
        AddEdgeOrbit(Gra, [iEXT,jEXT]);
        AddEdgeOrbit(Gra, [jEXT,iEXT]);
      fi;
    od;
  od;
  return Gra;
end);




InstallGlobalFunction(TranslateGroupExtToFac,
function(GroupExt, EXT, FAC)
  local ListDesc, eFac, ListInc, iExt;
  ListDesc:=[];
  for eFac in FAC
  do
    Add(ListDesc, Filtered([1..Length(EXT)], x->EXT[iExt]*eFac=0));
  od;
  return TranslateGroup(GroupExt, ListDesc, OnSets);
end);


InstallGlobalFunction(PersoGroupMatrix,
function(ListGen, n)
  if Length(ListGen)=0 then
    return Group(IdentityMat(n));
  else
    return Group(ListGen);
  fi;
end);



InstallGlobalFunction(SecondReduceGroupAction,
function(TheGroup, SmallSet)
  local ListGens, eGen, ListPos;
  ListGens:=[];
  if Length(SmallSet)<>Length(Set(SmallSet)) then
    Error("The input set has repetitions");
  fi;
  for eGen in GeneratorsOfGroup(TheGroup)
  do
    ListPos:=List(SmallSet, x->Position(SmallSet, OnPoints(x, eGen)));
    Add(ListGens, PermList(ListPos));
  od;
  return PersoGroupPerm(ListGens);
end);



# we complete a suitable vector family to
# a Z-spanning family of vectors
InstallGlobalFunction(SubspaceCompletion,
function(eBasis, n)
  local RSE, d, A1, A2, TheProd, A1bis, i, j, FullBasis, TheCompletion;
  RSE:=SmithNormalFormIntegerMatTransforms(eBasis);
  d:=Length(eBasis);
  if Length(eBasis)=0 then
    return IdentityMat(n);
  fi;
  if RankMat(eBasis)<>d then
    Error("The vector family is not linearly independent, no way to complete");
  fi;
  A1:=RSE.rowtrans;
  A2:=RSE.coltrans;
  TheProd:=A1*eBasis*A2;
  for i in [1..d]
  do
    if TheProd[i][i]<>1 then
      Print("The basis B is independent but does not Z-span QB inter Z^n\n");
      Error("So we cannot extend it to a full Z-basis");
    fi;
  od;
  A1bis:=NullMat(n,n);
  for i in [1..d]
  do
    for j in [1..d]
    do
      A1bis[i][j]:=A1[i][j];
    od;
  od;
  for i in [d+1..n]
  do
    A1bis[i][i]:=1;
  od;
  FullBasis:=Inverse(A1bis)*Inverse(A2);
  TheCompletion:=FullBasis{[d+1..n]};
  return TheCompletion;
end);

# Find an orthonormal basis to eBasis
InstallGlobalFunction(SubspaceCompletionRational,
function(eBasis, n)
  if Length(eBasis)=0 then
    return IdentityMat(n);
  fi;
  return NullspaceMat(TransposedMat(eBasis));
end);


InstallGlobalFunction(CongrMap,
function(eMat)
  return TransposedMat(Inverse(eMat));
end);



InstallGlobalFunction(IsCentrallySymmetric,
function(EXT)
  local eVert, eCent;
  eCent:=Sum(EXT)/Length(EXT);
  for eVert in EXT
  do
    if Position(EXT, 2*eCent-eVert)=fail then
      return false;
    fi;
  od;
  return true;
end);



InstallGlobalFunction(ProjectionFrame,
function(EXT)
  local rnk, EXTred;
  EXTred:=ShallowCopy(EXT);
  if TestConicness(EXTred) then
    Add(EXTred, FacetOfInfinity(Length(EXTred[1])) );
  fi;
  return ColumnReduction(EXTred, RankMat(EXTred)).Select;
end);



# return the largest integer p such that p^n <= C
InstallGlobalFunction(GetLowestPower,
function(n, C)
  local p;
  if C < 1 then
    Error("We need C greater or equal to 1");
  fi;
  p:=1;
  while(true)
  do
    if (p+1)^n > C then
      return p;
    fi;
    p:=p+1;
  od;
end);



InstallGlobalFunction(GetPositionAntipodal,
function(ListVect, eVect)
  local pos;
  pos:=Position(ListVect, eVect);
  if pos<>fail then
    return pos;
  fi;
  pos:=Position(ListVect, -eVect);
  if pos<>fail then
    return pos;
  fi;
  return fail;
end);



InstallGlobalFunction(GetListPermGens,
function(ListVect, ListMatrGens)
  local eSperm, ListPermGens, ListVectSet, ListVectRed, eMatrGen, ListVectImg, eNewPerm;
  eSperm:=SortingPerm(ListVect);
  ListPermGens:=[];
  ListVectRed:=ColumnReduction(ListVect).EXT;
  ListVectSet:=Set(ListVect);
  for eMatrGen in ListMatrGens
  do
    ListVectImg:=ListVectSet*eMatrGen;
    if Set(ListVectImg)<>ListVectSet then
      Error("The matrix eMatrGen does not preserve ListVect");
    fi;
    eNewPerm:=eSperm*SortingPerm(ListVectImg)*Inverse(eSperm);
    Add(ListPermGens, eNewPerm);
    if FindTransformation(ListVectRed, ListVectRed, eNewPerm)=fail then
      Error("Bug in the code of GetListPermGens");
    fi;
  od;
  return ListPermGens;
end);


# We use newton identities for converting the
# symmetric identities into power sums.
InstallGlobalFunction(GetNewtonSums,
function(ListE, ThePowExpo)
  local ListPowSums, TheDeg, k, GetEvalue, eSum, j;
  ListPowSums:=[];
  TheDeg:=Length(ListE);
  GetEvalue:=function(k)
    if k <= TheDeg then
      return ListE[k];
    fi;
    return 0;
  end;
  for k in [1..ThePowExpo]
  do
    if k=1 then
      eSum:=ListE[1];
    else
      eSum:=0;
      for j in [1..k-1]
      do
        eSum:=eSum + (-1)^(j-1)*GetEvalue(j)*ListPowSums[k-j];
      od;
      eSum:=eSum  +(-1)^(k-1)*k*GetEvalue(k);
    fi;
    Add(ListPowSums, eSum);
  od;
  return ListPowSums;
end);



InstallGlobalFunction(IsVectorIrreducible,
function(eVect)
  return GcdVector(eVect).TheGcd=1;
end);


InstallGlobalFunction(FindFacetInequalityGeneral,
function(EXT, ListIncidence, IsPos, RemoveFrac)
  local ListV, NLE, NSP, NewNSP, IsPosRes, IsNegRes, eVert, V, TheDim, eScal;
  ListV:=EXT{ListIncidence};
  if TestConicness(EXT) then
    TheDim:=Length(EXT[1]);
    V:=ListWithIdenticalEntries(TheDim,0);
    V[1]:=1;
    Add(ListV, V);
  fi;
  NLE:=NullspaceMat(TransposedMat(ListV));
  if Length(NLE)<>1 then
    return rec(success:=false, reason:=Concatenation("|NLE|=", Length(NLE), " instead of expected 1\n"));
  fi;
  NSP:=NLE[1];
  NewNSP:=RemoveFrac(NSP);
  IsPosRes:=true;
  IsNegRes:=true;
  for eVert in EXT
  do
    eScal:=eVert*NewNSP;
    if IsPos(eScal)=true then
      IsNegRes:=false;
    fi;
    if IsPos(-eScal)=true then
      IsPosRes:=false;
    fi;
  od;
  if IsNegRes=false and IsPosRes=false then
    return rec(success:=false, reason:="We can't have it both positive and negative, FacetError\n");
  fi;
  if IsPosRes=false then
    NewNSP:=-NewNSP;
  fi;
  return rec(success:=true, eIneq:=NewNSP);
end);



InstallGlobalFunction(FindFacetInequalityAndTest,
function(EXT, ListIncidence)
  local IsPos, RemoveFrac;
  IsPos:=function(x)
    return x>0;
  end;
  RemoveFrac:=RemoveFraction;
  return FindFacetInequalityGeneral(EXT, ListIncidence, IsPos, RemoveFrac);
end);



InstallGlobalFunction(FindFacetInequality,
function(EXT, ListIncidence)
  local IsPos, RemoveFrac, Nval;
  if IsMatrixRational(EXT)=true then
    IsPos:=function(x)
      return x>0;
    end;
    RemoveFrac:=RemoveFraction;
    return FindFacetInequalityGeneral(EXT, ListIncidence, IsPos, RemoveFrac).eIneq;
  fi;
end);

InstallGlobalFunction(GetIndexOfVectorFamily,
function(EXT)
  local n, NSP, TotalBasis, ListSol;
  n:=Length(EXT[1]);
  if RankMat(EXT)=n then
    return AbsInt(DeterminantMat(BaseIntMat(EXT)));
  fi;
  NSP:=NullspaceIntMat(TransposedMat(EXT));
  TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
  ListSol:=List(EXT, x->SolutionMat(TotalBasis,x));
  return AbsInt(DeterminantMat(BaseIntMat(ListSol)));
end);



InstallGlobalFunction(SYMPOL_PrintMatrix,
function(eFile, EXT)
  local output;
  output:=OutputTextFile(eFile, true);
  AppendTo(output, Length(EXT), " ", Length(EXT[1]), "\n");
  WriteMatrix(output, EXT);
  CloseStream(output);
end);


InstallGlobalFunction(SYMPOL_PrintGroup,
function(eFile, n, GRP)
  local ListGen, output, eGen, i, j;
  ListGen:=GeneratorsOfGroup(GRP);
  output:=OutputTextFile(eFile, true);
  AppendTo(output, n, " ", Length(ListGen), "\n");
  for eGen in ListGen
  do
    for i in [1..n]
    do
      j:=OnPoints(i, eGen);
      AppendTo(output, " ", j-1);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end);



InstallGlobalFunction(GetTranslationClasses,
function(eMat)
  local n, ListGen, ListTransClass, ListStatus, FuncInsert, nbClass, IsFinished, iClass, eClass, eGen;
  n:=Length(eMat[1]);
  ListGen:=IdentityMat(n);
  ListTransClass:=[];
  ListStatus:=[];
  FuncInsert:=function(eVect)
    local fVect, eSol;
    for fVect in ListTransClass
    do
      eSol:=SolutionIntMat(eMat, eVect - fVect);
      if eSol<>fail then
        return;
      fi;
    od;
    Add(ListTransClass, eVect);
    Add(ListStatus, 0);
  end;
  FuncInsert(ListWithIdenticalEntries(n,0));
  while(true)
  do
    nbClass:=Length(ListTransClass);
    IsFinished:=true;
    for iClass in [1..nbClass]
    do
      if ListStatus[iClass]=0 then
        ListStatus[iClass]:=1;
	IsFinished:=false;
        eClass:=ListTransClass[iClass];
	for eGen in ListGen
	do
	  FuncInsert(eClass + eGen);
	od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
    Print("Now |ListTransClass|=", Length(ListTransClass), "\n");
  od;
  return ListTransClass;
end);



InstallGlobalFunction(GetFunctionalityTranslationClasses,
function(TheLattice)
  local ListTrans, nbTrans, GetPosition;
  ListTrans:=GetTranslationClasses(TheLattice);
  nbTrans:=Length(ListTrans);
  GetPosition:=function(eTrans)
    local iTrans, eSol;
    for iTrans in [1..nbTrans]
    do
      eSol:=SolutionIntMat(TheLattice, eTrans - ListTrans[iTrans]);
      if eSol<>fail then
        return iTrans;
      fi;
    od;
    Error("Failed to find the iTrans");
  end;
  return rec(ListTrans:=ListTrans, GetPosition:=GetPosition);
end);



InstallGlobalFunction(DihedralCanonicalization,
function(eList)
  local MyDihedralGroup, len, GRP, O;
  MyDihedralGroup:=function(n)
    local eList1, eList2;
    eList1:=Concatenation([2..n],[1]);
    eList2:=Reversed([1..n]);
    return Group([PermList(eList1), PermList(eList2)]);
  end;
  len:=Length(eList);
  GRP:=MyDihedralGroup(len);
  O:=Orbit(GRP, eList, Permuted);
  return Minimum(O);
end);

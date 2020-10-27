# The "smith" program is obtained by compiling the example smith.C
# in linbox-1.3.2
FileCompLinboxSmith:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"smith");
FileCompLinboxRank:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"rank");
FileCompLinboxSolve:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"solve");
FileCompLinboxSmithvalence:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"smithvalence");
FileCompLinboxSmithToGap:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"SmithToGap");
FileCompLinboxRankToGap:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"RankToGap");
FileCompLinboxSmithvalenceToGap:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"SmithvalenceToGap");
FileCompLinboxNullspace:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"nullspace");
FileCompLinboxNullspaceRank:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"nullspace_rank");




GetGAPmatrixFromSparseMat:=function(SpMat)
  local nbLine, nbCol, RetMat, iLine, eEnt, len, i, iCol, eVal;
  nbLine:=SpMat.nbLine;
  nbCol:=SpMat.nbCol;
  RetMat:=NullMat(nbLine, nbCol);
  for iLine in [1..nbLine]
  do
    eEnt:=SpMat.ListEntries[iLine];
    len:=Length(eEnt.ListCol);
    for i in [1..len]
    do
      iCol:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      RetMat[iLine][iCol]:=eVal;
    od;
  od;
  return RetMat;
end;




# Adapted from the GAPhomology code in GAP.
PrintMatrixSparse:=function(FileName, TheMat)
  local ni, nj, i, j, output;
  ni := Length(TheMat);
  nj := Length(TheMat[1]);
  output := OutputTextFile(FileName, true );;
  AppendTo(output,ni," ",nj," M\n");
  for i in [1..ni] do
    for j in [1..nj] do
      if TheMat[i][j] <> 0 then
        AppendTo(output,i," ",j," ",TheMat[i][j],"\n");
      fi;
    od;
  od;
  AppendTo(output,"0 0 0\n");
  CloseStream(output);
end;



GetFactorLinbox:=function(RecMatrix)
  local TheMat, dim1, dim2, ListFactors, iDim, TheFileMat, TheFileOut, TheFileGap, nbCol, nbRow, TheCommand, eEnt, alpha, nb, iter, TheResult, TheMatRed;
  TheMat:=RecMatrix.TheMat;
  dim1:=RecMatrix.dim1;
  dim2:=RecMatrix.dim2;
  ListFactors:=[];
  if dim1=0 then
    ListFactors:=[];
    for iDim in [1..dim2]
    do
      Add(ListFactors, 0);
    od;
    return ListFactors;
  fi;
  if dim2=0 then
    return [];
  fi;
  TheFileMat:=Filename(POLYHEDRAL_tmpdir,"mat.txt");
  TheFileOut:=Filename(POLYHEDRAL_tmpdir,"out.txt");
  TheFileGap:=Filename(POLYHEDRAL_tmpdir,"out.gap");
#  Print("TheFileMat=", TheFileMat, "\n");
  nbCol:=Length(TheMat[1]);
  nbRow:=Length(TheMat);
  if TheMat=NullMat(nbRow, nbCol) then
    ListFactors:=[];
    for iter in [1..nbRow]
    do
      Add(ListFactors, "Z");
    od;
    return ListFactors;
  fi;
  PrintArray(TheMat);
  PrintArray(TheMatRed);
  TheMatRed:=GetZbasis(TheMat);
  PrintMatrixSparse(TheFileMat, TheMatRed);
  #
  TheCommand:=Concatenation(FileCompLinboxSmith, " adaptive 30 ", String(nbCol), " ", TheFileMat, " sparse > ", TheFileOut);
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileCompLinboxSmithToGap, " ", TheFileOut, " > ", TheFileGap);
  Exec(TheCommand);
  #
  TheResult:=ReadAsFunction(TheFileGap)();
  RemoveFileIfExist(TheFileMat);
  RemoveFileIfExist(TheFileOut);
  RemoveFileIfExist(TheFileGap);
  ListFactors:=[];
  for eEnt in TheResult
  do
    alpha:=eEnt[1];
    nb:=eEnt[2];
    if alpha<>1 then
      for iter in [1..nb]
      do
        Add(ListFactors, alpha);
      od;
    fi;
  od;
  return ListFactors;
end;


GetFactorDesc:=function(RecMatrix)
  local TheMat, dim1, dim2, ListFactors, nbFac, SNF, iFac, LCol, H, alpha, iDim;
  TheMat:=RecMatrix.TheMat;
  dim1:=RecMatrix.dim1;
  dim2:=RecMatrix.dim2;
  ListFactors:=[];
  if dim1=0 then
    ListFactors:=[];
    for iDim in [1..dim2]
    do
      Add(ListFactors, "Z");
    od;
    return ListFactors;
  fi;
  if dim2=0 then
    return [];
  fi;
  nbFac:=Length(TheMat[1]);
  SNF:=SmithNormalFormIntegerMat(TheMat);
  for iFac in [1..nbFac]
  do
    LCol:=List(SNF, x->x[iFac]);
    H:=Difference(Set(LCol), [0]);
    if H=[] then
      Add(ListFactors, 0);
    else
      if Length(H)>1 then
        Error("Some error somewheree");
      fi;
      alpha:=H[1];
      if alpha<>1 then
        Add(ListFactors, alpha);
      fi;
    fi;
  od;
  return ListFactors;
end;

#
# Compute the product SpMat1 * SpMat2
SPARSEMAT_ProductMatrix:=function(SpMat1, SpMat2)
  local nbLine1, nbCol1, nbLine2, nbCol2, NewListEntries, iLine, eVect, eEnt, i, iCol, eVal, iB, eEntB, ListIdx, iColB, eValB, NewEnt;
  nbLine1:=SpMat1.nbLine;
  nbCol1:=SpMat1.nbCol;
  nbLine2:=SpMat2.nbLine;
  nbCol2:=SpMat2.nbCol;
  if nbCol1<>nbLine2 then
    Error("The matrix sizes do not match");
  fi;
  NewListEntries:=[];
  for iLine in [1..nbLine1]
  do
    eVect:=ListWithIdenticalEntries(nbCol2, 0);
    eEnt:=SpMat1.ListEntries[iLine];
    for i in [1..Length(eEnt.ListVal)]
    do
      iCol:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      eEntB:=SpMat2.ListEntries[iCol];
      for iB in [1..Length(eEntB.ListVal)]
      do
        iColB:=eEntB.ListCol[iB];
        eValB:=eEntB.ListVal[iB];
        eVect[iColB]:=eVect[iColB] + eVal*eValB;
      od;
    od;
    ListIdx:=Filtered([1..nbCol2], x->eVect[x]<>0);
    NewEnt:=rec(ListCol:=ListIdx, ListVal:=eVect{ListIdx});
    Add(NewListEntries, NewEnt);
  od;
  return rec(nbLine:=nbLine1, nbCol:=nbCol2, ListEntries:=NewListEntries);
end;

SPARSEMAT_GetNNZ:=function(SpMat)
  local eNNZ, nbLine, iLine;
  eNNZ:=0;
  nbLine:=SpMat.nbLine;
  for iLine in [1..nbLine]
  do
    eNNZ:=eNNZ + Length(SpMat.ListEntries[iLine].ListVal);
  od;
  return eNNZ;
end;



SPARSEMAT_ZeroMatrix:=function(nbLine, nbCol)
  local ListEntries, iLine;
  ListEntries:=[];
  for iLine in [1..nbLine]
  do
    Add(ListEntries, rec(ListCol:=[], ListVal:=[]));
  od;
  return rec(nbLine:=nbLine, nbCol:=nbCol, ListEntries:=ListEntries);
end;


SPARSEMAT_Transpose:=function(eRecSparse)
  local ListEntries, nbLineRet, nbColRet, iLineRet, iLine, eEnt, len, i, iCol, eVal;
  ListEntries:=[];
  nbLineRet:=eRecSparse.nbCol;
  nbColRet:=eRecSparse.nbLine;
  for iLineRet in [1..nbLineRet]
  do
    Add(ListEntries, rec(ListCol:=[], ListVal:=[]));
  od;
  for iLine in [1..eRecSparse.nbLine]
  do
    eEnt:=eRecSparse.ListEntries[iLine];
    len:=Length(eEnt.ListCol);
    for i in [1..len]
    do
      iCol:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      Add(ListEntries[iCol].ListCol, iLine);
      Add(ListEntries[iCol].ListVal, eVal);
    od;
  od;
  return rec(nbLine:=nbLineRet, nbCol:=nbColRet, ListEntries:=ListEntries);
end;




SPARSEMAT_ColumnConcatenation:=function(SpMat1, SpMat2)
  local nbLine, nbCol1, nbCol2, ListEntries, NewListCol, NewListVal, eEnt, iLine;
  if SpMat1.nbLine<>SpMat2.nbLine then
    Error("Number of lines should be the same");
  fi;
  nbLine:=SpMat1.nbLine;
  nbCol1:=SpMat1.nbCol;
  nbCol2:=SpMat2.nbCol;
  ListEntries:=[];
  for iLine in [1..nbLine]
  do
    NewListCol:=Concatenation(SpMat1.ListEntries[iLine].ListCol, List(SpMat2.ListEntries[iLine].ListCol, x->x+nbCol1));
    NewListVal:=Concatenation(SpMat1.ListEntries[iLine].ListVal, SpMat2.ListEntries[iLine].ListVal);
    eEnt:=rec(ListCol:=NewListCol, ListVal:=NewListVal);
    Add(ListEntries, eEnt);
  od;
  return rec(nbLine:=nbLine, nbCol:=nbCol1 + nbCol2, ListEntries:=ListEntries);
end;


SPARSEMAT_IsZero:=function(SpMat)
  local nbLine, iLine, ListVal;
  nbLine:=SpMat.nbLine;
  for iLine in [1..nbLine]
  do
    ListVal:=SpMat.ListEntries[iLine].ListVal;
    if ListVal<>ListWithIdenticalEntries(Length(ListVal),0) then
      return false;
    fi;
  od;
  return true;
end;



# Compute xA
SPARSEMAT_ImageVector:=function(SpMat, eVect)
  local nbLine, nbCol, eImg, iLine, eEnt, i, iCol, eVal;
  nbLine:=SpMat.nbLine;
  nbCol:=SpMat.nbCol;
  if nbLine<>Length(eVect) then
    Error("Wrong sizes in the matrix product");
  fi;
  eImg:=ListWithIdenticalEntries(nbCol,0);
  for iLine in [1..nbLine]
  do
    eEnt:=SpMat.ListEntries[iLine];
    for i in [1..Length(eEnt.ListVal)]
    do
      iCol:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      eImg[iCol]:=eImg[iCol] + eVect[iLine]*eVal;
    od;
  od;
  return eImg;
end;



LINBOX_SparsePrint:=function(TheFile, RecSparse)
  local output, nbLine, nbCol, iLine, ListEnt, nbEnt, iEnt;
  RemoveFileIfExist(TheFile);
  output:=OutputTextFile(TheFile, true );
  nbLine:=RecSparse.nbLine;
  nbCol:=RecSparse.nbCol;
  AppendTo(output, nbLine, " ", nbCol, " M\n");
  for iLine in [1..nbLine]
  do
    ListEnt:=RecSparse.ListEntries[iLine];
    nbEnt:=Length(ListEnt.ListCol);
    for iEnt in [1..nbEnt]
    do
      AppendTo(output, iLine, " ", ListEnt.ListCol[iEnt], " ", ListEnt.ListVal[iEnt], "\n");
    od;
  od;
  AppendTo(output,"0 0 0\n");
  CloseStream(output);
end;


LINBOX_SparsePrintTranspose:=function(TheFile, RecSparse)
  local output, nbLine, nbCol, iLine, ListEnt, nbEnt, iEnt;
  RemoveFileIfExist(TheFile);
  output:=OutputTextFile(TheFile, true);
  nbLine:=RecSparse.nbLine;
  nbCol:=RecSparse.nbCol;
  AppendTo(output, nbCol, " ", nbLine, " M\n");
  for iLine in [1..nbLine]
  do
    ListEnt:=RecSparse.ListEntries[iLine];
    nbEnt:=Length(ListEnt.ListCol);
    for iEnt in [1..nbEnt]
    do
      AppendTo(output, ListEnt.ListCol[iEnt], " ", iLine, " ", ListEnt.ListVal[iEnt], "\n");
    od;
  od;
  AppendTo(output,"0 0 0\n");
  CloseStream(output);
end;


SPMAT_PrintMatrixForMatlab:=function(TheFile, RecSparse)
  local output, nbLine, nbCol, iLine, ListEnt, nbEnt, iEnt;
  nbLine:=RecSparse.nbLine;
  nbCol:=RecSparse.nbCol;
  RemoveFileIfExist(TheFile);
  output:=OutputTextFile(TheFile, true);
  nbEnt:=Sum(List(RecSparse.ListEntries, x->Length(x.ListVal)));
  AppendTo(output, nbLine, " ", nbCol, " ", nbEnt, "\n");
  for iLine in [1..nbLine]
  do
    ListEnt:=RecSparse.ListEntries[iLine];
    nbEnt:=Length(ListEnt.ListCol);
    for iEnt in [1..nbEnt]
    do
      AppendTo(output, iLine, " ", ListEnt.ListCol[iEnt], " ", GetFractionAsReal(ListEnt.ListVal[iEnt]), "\n");
    od;
  od;
  CloseStream(output);
end;


CPP_PrintSparseMatrix:=function(TheFile, RecSparse)
  local output, nbLine, nbCol, iLine, ListEnt, nbEnt, iEnt, iCol, eVal;
  nbLine:=RecSparse.nbLine;
  nbCol:=RecSparse.nbCol;
  RemoveFileIfExist(TheFile);
  output:=OutputTextFile(TheFile, true);
  nbEnt:=Sum(List(RecSparse.ListEntries, x->Length(x.ListVal)));
  AppendTo(output, nbLine, " ", nbCol, " ", nbEnt, "\n");
  for iLine in [1..nbLine]
  do
    ListEnt:=RecSparse.ListEntries[iLine];
    nbEnt:=Length(ListEnt.ListCol);
    for iEnt in [1..nbEnt]
    do
      iCol:=ListEnt.ListCol[iEnt];
      eVal:=ListEnt.ListVal[iEnt] + 0.0;
      AppendTo(output, iLine-1, " ", iCol-1, " ", eVal, "\n");
    od;
  od;
  CloseStream(output);
end;



CPP_PrintVector:=function(TheFile, eVect)
  local output, TheDim, i, eVal;
  RemoveFileIfExist(TheFile);
  output:=OutputTextFile(TheFile, true);
  TheDim:=Length(eVect);
  AppendTo(output, TheDim, "\n");
  for i in [1..TheDim]
  do
    eVal:=eVect[i] + 0.0;
    AppendTo(output, eVal, "\n");
  od;
  CloseStream(output);
end;



SPMAT_PrintVectorForMatlab:=function(TheFile, eVect)
  local output, TheDim, i;
  RemoveFileIfExist(TheFile);
  output:=OutputTextFile(TheFile, true);
  TheDim:=Length(eVect);
  for i in [1..TheDim]
  do
    AppendTo(output, GetFractionAsReal(eVect[i]), "\n");
  od;    
  CloseStream(output);
end;


GetRankLinboxSparse:=function(RecSparseMat, pVal)
  local TheFileMat, TheFileOut, TheFileErr, TheFileGap, eStrP, TheCommand, TheResult, DenseMat;
  if FileCompLinboxRank=fail then
    DenseMat:=GetGAPmatrixFromSparseMat(RecSparseMat);
    return RankMat(DenseMat);
  else
    TheFileMat:=Filename(POLYHEDRAL_tmpdir,"mat.txt");
    TheFileOut:=Filename(POLYHEDRAL_tmpdir,"out.txt");
    TheFileErr:=Filename(POLYHEDRAL_tmpdir,"err.txt");
    TheFileGap:=Filename(POLYHEDRAL_tmpdir,"out.gap");
    RemoveFileIfExist(TheFileMat);
    RemoveFileIfExist(TheFileOut);
    RemoveFileIfExist(TheFileErr);
    RemoveFileIfExist(TheFileGap);
#    Print("TheFileMat=", TheFileMat, "\n");
    LINBOX_SparsePrint(TheFileMat, RecSparseMat);
    #
    if pVal=0 then
      eStrP:="";
    else
      eStrP:=Concatenation(" ", String(pVal));
    fi;
    #
    TheCommand:=Concatenation(FileCompLinboxRank, " ", TheFileMat, eStrP, " > ", TheFileOut, " 2> ", TheFileErr);
    Exec(TheCommand);
    #
    TheCommand:=Concatenation(FileCompLinboxRankToGap, " ", TheFileOut, " > ", TheFileGap);
    Exec(TheCommand);
    #
    TheResult:=ReadAsFunction(TheFileGap)();
    RemoveFileIfExist(TheFileMat);
    RemoveFileIfExist(TheFileOut);
    RemoveFileIfExist(TheFileErr);
    RemoveFileIfExist(TheFileGap);
    return TheResult;
  fi;
end;


#
# Get a set eSet of lines such that
# ListEntries{eSet} is of the same rank as the full matrix
#
LINBOX_GetDefininingLines:=function(RecSparseMat, pVal)
  local nbLine, TheRank, dimKernel, GetRankSubset, ReturnSet, iLine, NewSet, RankRed;
  nbLine:=RecSparseMat.nbLine;
  TheRank:=GetRankLinboxSparse(RecSparseMat, pVal);
  dimKernel:=nbLine - TheRank;
  Print("nbLine=", nbLine, "\n");
  Print("TheRank=", TheRank, "\n");
  Print("dimKernel=", dimKernel, "\n");
  if TheRank=nbLine then
    return [1..nbLine];
  fi;
  GetRankSubset:=function(TheSet)
    local NewSparseMat;
    NewSparseMat:=rec(nbLine:=Length(TheSet), nbCol:=RecSparseMat.nbCol, ListEntries:=RecSparseMat.ListEntries{TheSet});
    return GetRankLinboxSparse(NewSparseMat, pVal);
  end;
  ReturnSet:=[1..nbLine];
  for iLine in [1..nbLine]
  do
    Print("iLine=", iLine, " / ", nbLine, "\n");
    NewSet:=Difference(ReturnSet, [iLine]);
    RankRed:=GetRankSubset(NewSet);
    if RankRed=TheRank then
      ReturnSet:=NewSet;
      if Length(ReturnSet)=TheRank then
        return ReturnSet;
      fi;
    fi;
  od;
  Error("We should not reach that stage");
end;



LINBOX_SolveLinearSystem:=function(RecSparseMat, eVect)
  local TheFileMat, TheFileVec, TheFileOut, TheFileErr, TheFileGap, nbLine, nbCol, output, iCol, pVal, TheSol, TheCommand;
  TheFileMat:=Filename(POLYHEDRAL_tmpdir,"mat.txt");
  TheFileVec:=Filename(POLYHEDRAL_tmpdir,"vec.txt");
  TheFileOut:=Filename(POLYHEDRAL_tmpdir,"out.txt");
  TheFileErr:=Filename(POLYHEDRAL_tmpdir,"err.txt");
  TheFileGap:=Filename(POLYHEDRAL_tmpdir,"gap.txt");
  RemoveFileIfExist(TheFileMat);
  RemoveFileIfExist(TheFileVec);
  RemoveFileIfExist(TheFileOut);
  RemoveFileIfExist(TheFileErr);
  RemoveFileIfExist(TheFileGap);
  nbLine:=RecSparseMat.nbLine;
  nbCol:=RecSparseMat.nbCol;
  LINBOX_SparsePrint(TheFileMat, RecSparseMat);
  #
  output:=OutputTextFile(TheFileVec, true);
  for iCol in [1..nbCol]
  do
    AppendTo(output, " ", eVect[iCol]);
  od;
  CloseStream(output);
  #
  pVal:=0;
  TheCommand:=Concatenation(FileCompLinboxSolve, " ", TheFileMat, " ", TheFileVec, " ", String(pVal), " > ", TheFileOut, " 2> ", TheFileErr);
  Exec(TheCommand);
  
  Print(NullMat(5));
  #
  RemoveFileIfExist(TheFileMat);
  RemoveFileIfExist(TheFileVec);
  RemoveFileIfExist(TheFileOut);
  RemoveFileIfExist(TheFileErr);
  RemoveFileIfExist(TheFileGap);
  return TheSol;
end;

LINBOX_Nullspace:=function(RecSparseMat)
  local nbLine, nbCol, pVal, eSet, RedSparseMat, eDiff, DimSpace, TheNSP, iSpace, iLine, eVect, eEnt, len, i, eSol, eNSP;
  nbLine:=RecSparseMat.nbLine;
  nbCol:=RecSparseMat.nbCol;
  pVal:=0;
  eSet:=LINBOX_GetDefininingLines(RecSparseMat, pVal);
  RedSparseMat:=rec(nbLine:=Length(eSet), nbCol:=RecSparseMat.nbCol, ListEntries:=RecSparseMat.ListEntries{eSet});
  eDiff:=Difference([1..nbLine], eSet);
  DimSpace:=Length(eDiff);
  TheNSP:=[];
  for iSpace in [1..DimSpace]
  do
    iLine:=eDiff[iSpace];
    eVect:=ListWithIdenticalEntries(nbCol,0);
    eEnt:=RecSparseMat.ListEntries[iLine];
    len:=Length(eEnt.ListCol);
    for i in [1..len]
    do
      eVect[eEnt.ListCol[i]]:=eEnt.ListVal[i];
    od;
    eSol:=LINBOX_SolveLinearSystem(RedSparseMat, eVect);
    eNSP:=ListWithIdenticalEntries(nbLine,0);
    eNSP[iLine]:=1;
    eNSP{eSet}:=-eSol;
    Add(TheNSP, eNSP);
  od;
  return TheNSP;
end;


LINBOX_SmithMethod:=function(RecSparseMat)
  local TheFileMat, TheFileOut, TheFileErr, TheFileGap, TheCommand, TheResult, nbLine, nbCol;
  nbLine:=RecSparseMat.nbLine;
  nbCol:=RecSparseMat.nbCol;
  TheFileMat:=Filename(POLYHEDRAL_tmpdir,"mat.txt");
  TheFileOut:=Filename(POLYHEDRAL_tmpdir,"out.txt");
  TheFileErr:=Filename(POLYHEDRAL_tmpdir,"err.txt");
  TheFileGap:=Filename(POLYHEDRAL_tmpdir,"out.gap");
  RemoveFileIfExist(TheFileMat);
  RemoveFileIfExist(TheFileOut);
  RemoveFileIfExist(TheFileErr);
  RemoveFileIfExist(TheFileGap);
  LINBOX_SparsePrint(TheFileMat, RecSparseMat);
  #
  TheCommand:=Concatenation(FileCompLinboxSmith, " adaptive 30 ", String(nbCol), " ", TheFileMat, " sparse > ", TheFileOut);
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileCompLinboxSmithToGap, " ", TheFileOut, " > ", TheFileGap);
  Exec(TheCommand);
  #
  TheResult:=ReadAsFunction(TheFileGap)();
  RemoveFileIfExist(TheFileMat);
  RemoveFileIfExist(TheFileOut);
  RemoveFileIfExist(TheFileGap);
  return TheResult;
end;





LINBOX_SmithValenceMethod:=function(RecSparseMat)
  local TheFileMat, TheFileOut, TheFileErr, TheFileGap, TheCommand, TheResult, DenseMat, SNF, nbRel, TheDiag, TheDiagFilt, nbLine, nbCol;
  nbLine:=RecSparseMat.nbLine;
  nbCol:=RecSparseMat.nbCol;
  if FileCompLinboxSmithvalence=fail then
    DenseMat:=GetGAPmatrixFromSparseMat(RecSparseMat);
    SNF:=SmithNormalFormIntegerMat(DenseMat);
    nbRel:=Minimum(nbLine, nbCol);
    TheDiag:=List([1..nbRel], x->SNF[x][x]);
    TheDiagFilt:=Filtered(TheDiag, x->x<>0 and x<>1);
    return Collected(TheDiagFilt);
  else
    TheFileMat:=Filename(POLYHEDRAL_tmpdir,"mat.txt");
    TheFileOut:=Filename(POLYHEDRAL_tmpdir,"out.txt");
    TheFileErr:=Filename(POLYHEDRAL_tmpdir,"err.txt");
    TheFileGap:=Filename(POLYHEDRAL_tmpdir,"out.gap");
    RemoveFileIfExist(TheFileMat);
    RemoveFileIfExist(TheFileOut);
    RemoveFileIfExist(TheFileErr);
    RemoveFileIfExist(TheFileGap);
    LINBOX_SparsePrint(TheFileMat, RecSparseMat);
    TheCommand:=Concatenation(FileCompLinboxSmithvalence, " ", TheFileMat, " -ata > ", TheFileOut, " 2> ", TheFileErr);
#    Print("TheCommand=", TheCommand, "\n");
    Exec(TheCommand);
    #
    TheCommand:=Concatenation(FileCompLinboxSmithvalenceToGap, " ", TheFileErr, " > ", TheFileGap);
    Exec(TheCommand);
    #
    TheResult:=ReadAsFunction(TheFileGap)();
    if TheResult=fail then
      Error("Please debug from that point");
    fi;
    RemoveFileIfExist(TheFileMat);
    RemoveFileIfExist(TheFileOut);
    RemoveFileIfExist(TheFileErr);
    RemoveFileIfExist(TheFileGap);
    return TheResult;
  fi;
end;



GetFactorLinboxSparse:=function(RecSparseMat)
  local TheMat, nbLine, iDim, TheFileMat, TheFileOut, TheFileGap, nbCol, nbRow, TheCommand, eEnt, alpha, nb, iter, TheResult, TheMatRed, output, TheTorsion, rankFree, TheFileErr, iLine, ListEnt, nbEnt, iEnt, TheChoice, TheRank, MaxRank, KerRank, ElemDiv;
  nbLine:=RecSparseMat.nbLine;
  nbCol:=RecSparseMat.nbCol;
  if nbLine=0 then
    return rec(Torsion:=[], rankFree:=nbCol, rankMat:=0, ElemDiv:=[]);
  fi;
  if nbCol=0 then
    return rec(Torsion:=[], rankFree:=0, rankMat:=0, ElemDiv:=[]);
  fi;
  TheFileMat:=Filename(POLYHEDRAL_tmpdir,"mat.txt");
  TheFileOut:=Filename(POLYHEDRAL_tmpdir,"out.txt");
  TheFileErr:=Filename(POLYHEDRAL_tmpdir,"err.txt");
  TheFileGap:=Filename(POLYHEDRAL_tmpdir,"out.gap");
  RemoveFileIfExist(TheFileMat);
  RemoveFileIfExist(TheFileOut);
  RemoveFileIfExist(TheFileErr);
  RemoveFileIfExist(TheFileGap);
  LINBOX_SparsePrint(TheFileMat, RecSparseMat);
  #
  TheChoice:="SmithValence";
  if TheChoice="Smith" then
    TheResult:=LINBOX_SmithMethod(RecSparseMat);
  fi;
  if TheChoice="SmithValence" then
    TheResult:=LINBOX_SmithValenceMethod(RecSparseMat);
    #
    TheRank:=GetRankLinboxSparse(RecSparseMat, 0);
    MaxRank:=Minimum(nbLine, nbCol);
    KerRank:=MaxRank - TheRank;
    if nbCol > nbLine then
      KerRank:=KerRank + nbCol - nbLine;
    fi;
    Add(TheResult, [0, KerRank]);
  fi;
  TheTorsion:=[];
  rankFree:=0;
  ElemDiv:=[];
  for eEnt in TheResult
  do
    alpha:=eEnt[1];
    nb:=eEnt[2];
    if alpha<>0 then
      for iter in [1..nb]
      do
        Add(ElemDiv, alpha);
      od;
    fi;
    if alpha<>1 then
      for iter in [1..nb]
      do
        if alpha=0 then
          rankFree:=rankFree+1;
        else
          Add(TheTorsion, alpha);
        fi;
      od;
    fi;
  od;
  return rec(Torsion:=TheTorsion, rankFree:=rankFree, rankMat:=Length(ElemDiv), ElemDiv:=ElemDiv);
end;


RandomIntegralMatrix:=function(nbLine, nbCol, eSpread)
  local eMat, iLine, iCol;
  eMat:=NullMat(nbLine, nbCol);
  for iLine in [1..nbLine]
  do
    for iCol in [1..nbCol]
    do
      eMat[iLine][iCol]:=Random([-eSpread..eSpread]);
    od;
  od;
  return eMat;
end;


MatrixToSparse:=function(eMat)
  local nbLine, nbCol, ListEntries, eLine, ListCol, ListVal, eVal, eEnt, iCol;
  nbLine:=Length(eMat);
  nbCol:=Length(eMat[1]);
  ListEntries:=[];
  for eLine in eMat
  do
    ListCol:=[];
    ListVal:=[];
    for iCol in [1..nbCol]
    do
      eVal:=eLine[iCol];
      if eVal<>0 then
        Add(ListCol, iCol);
        Add(ListVal, eVal);
      fi;
    od;
    eEnt:=rec(ListCol:=ListCol, ListVal:=ListVal);
    Add(ListEntries, eEnt);
  od;
  return rec(nbLine:=nbLine, nbCol:=nbCol, ListEntries:=ListEntries);
end;



GetFactorDescSparse:=function(RecSparseMat)
  local TheMat, nbLine, nbCol, SNF, alpha, iDim, eEnt, TheTorsion, rankFree, iLine, eLine, UpperRank, ListEnt, iEnt, nbEnt, ElemDiv;
  nbLine:=RecSparseMat.nbLine;
  nbCol:=RecSparseMat.nbCol;
  if nbLine=0 then
    return rec(Torsion:=[], rankFree:=nbCol, rankMat:=0, ElemDiv:=[]);
  fi;
  if nbCol=0 then
    return rec(Torsion:=[], rankFree:=0, rankMat:=0, ElemDiv:=[]);
  fi;
  TheMat:=NullMat(nbLine, nbCol);
  for iLine in [1..nbLine]
  do
    ListEnt:=RecSparseMat.ListEntries[iLine];
    nbEnt:=Length(ListEnt.ListCol);
    for iEnt in [1..nbEnt]
    do
      TheMat[iLine][ListEnt.ListCol[iEnt]]:=ListEnt.ListVal[iEnt];
    od;
  od;
  SNF:=SmithNormalFormIntegerMat(TheMat);
  TheTorsion:=[];
  if nbCol > nbLine then
    rankFree:=nbCol - nbLine;
  else
    rankFree:=0;
  fi;
  UpperRank:=Minimum(nbLine, nbCol);
  ElemDiv:=[];
  for iLine in [1..UpperRank]
  do
    eLine:=SNF[iLine];
    alpha:=eLine[iLine];
    if alpha<>0 then
      Add(ElemDiv, alpha);
    fi;
    if eLine{Difference([1..nbCol], [iLine])}<>ListWithIdenticalEntries(nbCol-1,0) then
      Error("Some error in our conception of Smith Normal Form");
    fi;
    if alpha<>1 then
      if alpha=0 then
        rankFree:=rankFree+1;
      else
        Add(TheTorsion, alpha);
      fi;
    fi;
  od;
  return rec(Torsion:=TheTorsion, rankFree:=rankFree, rankMat:=Length(ElemDiv), ElemDiv:=ElemDiv);
end;









# we should have M1 * M2 = 0 
GetQuotientRecMatrix:=function(M1, M2, dim1, dim2, dim3)
  local TheKerBasis, NewMat, eLine, B, SNF, MyIdentityMat, UseGAP, UseLINBOX, TheQuot, RecMatrix;
  MyIdentityMat:=function(n)
    if n=0 then
      return [];
    fi;
    return IdentityMat(n);
  end;
  if dim3=0 then
    TheKerBasis:=MyIdentityMat(dim2);
  else
    if dim2=0 then
      TheKerBasis:=[];
    else
      TheKerBasis:=NullspaceIntMat(M2);
    fi;
  fi;
  NewMat:=[];
  for eLine in M1
  do
    if dim2=0 then
      B:=[];
    else
      if Length(TheKerBasis)=0 then
        B:=[];
      else
        B:=SolutionMat(TheKerBasis, eLine);
      fi;
    fi;
    Add(NewMat, B);
  od;
  return rec(dim1:=dim1, dim2:=Length(TheKerBasis), TheMat:=NewMat);
end;



GetQuotient:=function(M1, M2, dim1, dim2, dim3)
  local RecMatrix, UseGAP, UseLINBOX, TheQuot;
  RecMatrix:=GetQuotientRecMatrix(M1, M2, dim1, dim2, dim3);
  UseGAP:=true;
  if UseGAP then
    TheQuot:=GetFactorDesc(RecMatrix);
  fi;
#  UseLINBOX:=true;
#  if UseLINBOX then
#    TheQuot:=GetFactorLinbox(RecMatrix);
#  fi;
  return TheQuot;
end;




GettingHomologiesFromKilledMatrices:=function(ListDimensions, ListMatrixDoperators)
  local ListHomologies, iRank, TheHomology, kSought;
  ListHomologies:=[];
  kSought:=Length(ListMatrixDoperators)-2;
  for iRank in [0..kSought]
  do
    TheHomology:=GetQuotient(ListMatrixDoperators[iRank+2], ListMatrixDoperators[iRank+1], ListDimensions[iRank+3], ListDimensions[iRank+2], ListDimensions[iRank+1]);
    Add(ListHomologies, TheHomology);
  od;
  return ListHomologies;
end;

GettingRecMatricesFromKilledMatrices_coho:=function(ListDimensions, ListMatrixDoperators)
  local ListRecMatrix, iRank, kSought, RecMatrix;
  Print("Begin GettingRecMatricesFromKilledMatrices_coho\n");
  ListRecMatrix:=[];
  kSought:=Length(ListMatrixDoperators)-2;
  for iRank in [0..kSought]
  do
    RecMatrix:=GetQuotientRecMatrix(ListMatrixDoperators[iRank+1], ListMatrixDoperators[iRank+2], ListDimensions[iRank+1], ListDimensions[iRank+2], ListDimensions[iRank+3]);
    Add(ListRecMatrix, RecMatrix);
  od;
  Print("End GettingRecMatricesFromKilledMatrices_coho\n");
  return ListRecMatrix;
end;


GettingStringFromVec:=function(TotHomoNr)
  local TotHomoStr, eHom, eStr;
  TotHomoStr:=[];
  for eHom in TotHomoNr
  do
    if eHom=0 then
      eStr:="Z";
    else
      eStr:=Concatenation("Z/", String(eHom), "Z");
    fi;
    Add(TotHomoStr, eStr);
  od;
  return TotHomoStr;
end;

GettingStringFromVecBis:=function(TotHomoNr)
  local GetBasicString, eColl, ListStr, eEnt, eMult, eHom, eStrA, eStrB, eStrRet, i;
  GetBasicString:=function(eHom)
    if eHom=0 then
      return "\\ZZ";
    else
      return Concatenation("\\ZZ_{", String(eHom), "}");
    fi;
  end;
  eColl:=Collected(TotHomoNr);
  ListStr:=[];
  for eEnt in eColl
  do
    eMult:=eEnt[2];
    eHom:=eEnt[1];
    eStrA:=GetBasicString(eHom);
    if eMult>1 then
      eStrB:=Concatenation(eStrA, "^{", String(eMult), "}");
    else
      eStrB:=eStrA;
    fi;
    Add(ListStr, eStrB);
  od;
#  for i in [1..Length(ListStr)]
#  do
#    Print("i=", i, " str=", ListStr[i], "\n");
#  od;
  if Length(ListStr)=0 then
    return "0";
  else
    eStrRet:=ListStr[1];
    for i in [2..Length(ListStr)]
    do
      eStrRet:=Concatenation(eStrRet, " \\oplus ", ListStr[i]);
    od;
    return eStrRet;
  fi;
end;




GettingCohomologyFromSparseMatrices:=function(ListSparseMat)
  local kSought, ListSNF, nbLine, nbCol, eSNF, ListCOHO, iRank, TheTorsion, DimTot_Rel, rankFree, DimImg, DimKer_Rel, DimImg_Rel, rankHomology_Rel, TotHomology, eSparseMat, ListNNZ, ListRankFree, eNNZ, ListCOHObis, ListElemDiv, ListRankMat;
  kSought:=Length(ListSparseMat)-2;
  ListSNF:=[];
  ListNNZ:=[];
  ListRankMat:=[];
  ListRankFree:=[];
  ListElemDiv:=[];
  for eSparseMat in ListSparseMat
  do
    nbLine:=eSparseMat.nbLine;
    nbCol:=eSparseMat.nbCol;
#    if nbLine + nbCol < 40 then
      eSNF:=GetFactorDescSparse(eSparseMat);
#    else
#      eSNF:=GetFactorLinboxSparse(eSparseMat);
#    fi;
    eNNZ:=SPARSEMAT_GetNNZ(eSparseMat);
    Add(ListSNF, eSNF);
    Add(ListRankFree, eSNF.rankFree);
    Add(ListRankMat, eSNF.rankMat);
    Add(ListNNZ, eNNZ);
    Add(ListElemDiv, eSNF.ElemDiv);
  od;
  ListCOHO:=[ ["Z"] ];
  ListCOHObis:=[ "\\ZZ" ];
  for iRank in [0..kSought]
  do
    TheTorsion:=ListSNF[iRank+1].Torsion;
    DimTot_Rel:=ListSparseMat[iRank+1].nbCol;
    rankFree:=ListSNF[iRank+2].rankFree;
    DimImg:=ListSparseMat[iRank+2].nbCol - rankFree;
    DimKer_Rel:=DimTot_Rel - DimImg; # Rank theorem
    DimImg_Rel:=DimTot_Rel - ListSNF[iRank+1].rankFree;
    rankHomology_Rel:=DimKer_Rel - DimImg_Rel;
    TotHomology:=Concatenation(TheTorsion, ListWithIdenticalEntries(rankHomology_Rel, 0));
    Add(ListCOHO, GettingStringFromVec(TotHomology));
    Add(ListCOHObis, GettingStringFromVecBis(TotHomology));
  od;
  return rec(ListCOHO:=ListCOHO,
             ListCOHObis:=ListCOHObis, 
             ListRankFree:=ListRankFree, 
             ListRankMat:=ListRankMat, 
             ListNNZ:=ListNNZ, 
             ListElemDiv:=ListElemDiv);
end;


GettingCohomologiesFromKilledMatrices:=function(ListDimensions, ListMatrixDoperators)
  local ListRecMatrix;
  ListRecMatrix:=GettingRecMatricesFromKilledMatrices_coho(ListDimensions, ListMatrixDoperators);
  return List(ListRecMatrix, GetFactorDesc);
end;


CheckSNF_algo:=function(eMat)
  local RecSparse, eReply1, eReply2;
  RecSparse:=MatrixToSparse(eMat);
  eReply1:=GetFactorDescSparse(RecSparse);
  eReply2:=GetFactorLinboxSparse(RecSparse);
  if eReply1<>eReply2 then
    Error("Please debug the SNF algos");
  fi;
  return eReply1;
end;

EyeMatrix:=function(nbLine, nbCol)
  local eMat, i, j, eLine;
  eMat:=[];
  for i in [1..nbLine]
  do
    eLine:=[];
    for j in [1..nbCol]
    do
      Add(eLine, 1);
    od;
    Add(eMat, eLine);
  od;
  return eMat;
end;

ExtendedAmatrix:=function(n,k)
  local ListEntries, iLine, ListCol, ListVal, iShift, iCol, eVal, eEntry;
  ListEntries:=[];
  for iLine in [1..n]
  do
    ListCol:=[];
    ListVal:=[];
    for iShift in [-k..k]
    do
      iCol:=iLine+iShift;
      if iCol >= 1 and iCol <= n then
        if iShift>0 then
          eVal:=k+1-iShift;
        else
          eVal:=k+1+iShift;
        fi;
        Add(ListCol, iCol);
        Add(ListVal, eVal);
      fi;
    od;
    eEntry:=rec(ListCol:=ListCol, ListVal:=ListVal);
    Add(ListEntries, eEntry);
  od;
  return rec(nbLine:=n, nbCol:=n, ListEntries:=ListEntries);
end;


#
#
# We try to finf a vector of short norm such that
# v*TheMat = TheVect
SolutionIntMatShort:=function(TheMat_pre, TheVect_pre)
  local eSol, eSol_B, Strategy_LLL, TheMult1, TheMult2, TheMult, TheMat, TheVect;
  TheMult1:=RemoveFractionMatrixPlusCoef(TheMat_pre).TheMult;
  TheMult2:=RemoveFractionPlusCoef(TheVect_pre).TheMult;
  TheMult:=LcmInt(TheMult1, TheMult2);
  TheMat:=TheMat_pre*TheMult;
  TheVect:=TheVect_pre*TheMult;
  eSol:=SolutionIntMat(TheMat, TheVect);
  if eSol=fail then
    return fail;
  fi;
  Strategy_LLL:=function()
    local TheConcat, eLLL, eRelation, eVal, eSol, len;
    TheConcat:=Concatenation(TheMat, [TheVect]);
    len:=Length(TheConcat);
    eLLL:=LLLReducedBasis(TheConcat, "linearcomb");
    for eRelation in eLLL.relations
    do
      eVal:=eRelation[len];
      if AbsInt(eVal)=1 then
        eSol:=-eRelation{[1..len-1]}/eVal;
        if eSol*TheMat<>TheVect then
          Error("Wrong vector found");
        fi;
        return eSol;
      fi;
    od;
    return fail;
  end;
  eSol_B:=Strategy_LLL();
  if eSol_B<>fail then
    return eSol_B;
  fi;
  Print("We failed, used plan-A\n");
  return eSol;
end;


TestSpeedExtendedSmith:=function(n,k)
  local eSp, eTime1, eTime2, TheDesc;
  eSp:=ExtendedAmatrix(n,k);
  eTime1:=GetDate();
  TheDesc:=GetFactorLinboxSparse(eSp);
  eTime2:=GetDate();
  Print("time=", eTime2-eTime1, "\n");
  return TheDesc;
end;





PrintHomologyGroup:=function(output, eHom)
  local eColl, nbEnt, iEnt, eMult, eVal;
  if eHom=[] then
    AppendTo(output, "0");
  else
    eColl:=Collected(eHom);
    nbEnt:=Length(eColl);
    for iEnt in [1..nbEnt]
    do
      eMult:=eColl[iEnt][2];
      eVal:=eColl[iEnt][1];
      if iEnt>1 then
        AppendTo(output, " + ");
      fi;
      if eMult=1 then
        AppendTo(output, eVal);
      else
        AppendTo(output, eMult, eVal);
      fi;
    od;
  fi;
end;




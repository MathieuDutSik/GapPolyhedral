MAGMA_PrintRationalMatrix:=function(output, TheMat)
  local nbRow, nbCol, iRow, iCol, eVal, eExpr, eStr, IsFirst;
  nbRow:=Length(TheMat);
  nbCol:=Length(TheMat[1]);
  AppendTo(output, "Matrix(RationalField(),", nbRow, ",", nbCol, ",[");
  eStr:="";
  IsFirst:=1;
  for iRow in [1..nbRow]
  do
    for iCol in [1..nbCol]
    do
      if IsFirst=0 then
        eStr:=Concatenation(eStr, ",");
      fi;
      IsFirst:=0;
      eStr:=Concatenation(eStr, String(TheMat[iRow][iCol]));
    od;
  od;
  WriteAll(output, eStr);
  AppendTo(output, "])");
end;

PrintMat_GetLengthPosInt:=function(eNB)
  local len;
  len:=1;
  while(true)
  do
    if eNB < 10^(len) then
      return len;
    fi;
    len:=len+1;
  od;
end;

PrintMat_PrintPosIntFixedLength:=function(output, FixedLen, eInt)
  local len, i;
  len:=PrintMat_GetLengthPosInt(eInt);
  for i in [len+1..FixedLen]
  do
    AppendTo(output, " ");
  od;
  AppendTo(output, eInt);
end;

PrintMat_NiceMatrixPrinting:=function(output, TheMat)
  local siz1, siz2, i1, i2, MaxLen, len;
  siz1:=Length(TheMat);
  siz2:=Length(TheMat[1]);
  MaxLen:=1;
  for i1 in [1..siz1]
  do
    for i2 in [1..siz2]
    do
      len:=PrintMat_GetLengthPosInt(TheMat[i1][i2]);
      MaxLen:=Maximum(MaxLen, len);
    od;
  od;
  for i1 in [1..siz1]
  do
    for i2 in [1..siz2]
    do
      AppendTo(output, " ");
      PrintMat_PrintPosIntFixedLength(output, MaxLen, TheMat[i1][i2]);
    od;
    AppendTo(output, "\n");
  od;
end;


SAGE_AnnaPrintMatrix:=function(FileOut, ListMat)
  local output, iMat, nbMat, eMat, dim, iLine, iCol;
  RemoveFileIfExist(FileOut);
  output:=OutputTextFile(FileOut, true);
  nbMat:=Length(ListMat);
  AppendTo(output, "data = [\n");
  for iMat in [1..nbMat]
  do
    AppendTo(output, "Matrix(");
    eMat:=ListMat[iMat];
    dim:=Length(eMat);
    #
    AppendTo(output, "[");
    for iLine in [1..dim]
    do
      AppendTo(output, "[");
      for iCol in [1..dim]
      do
        AppendTo(output, eMat[iLine][iCol]);
	if iCol<dim then
	  AppendTo(output, ", ");
	fi;
      od;
      AppendTo(output, "]");
      if iLine<dim then
        AppendTo(output, ", ");
      fi;
    od;
    AppendTo(output, "]");
    #
    AppendTo(output, ")");
    if iMat<nbMat then
      AppendTo(output, ",\\\n");
    fi;
  od;
  AppendTo(output, "]\n");
  CloseStream(output);
end;


SAGE_PrintMatrix:=function(output, eMat)
  local nbLine, nbCol, iLine, iCol;
  nbLine:=Length(eMat);
  nbCol:=Length(eMat[1]);
  AppendTo(output, "matrix([");
  for iLine in [1..nbLine]
  do
    if iLine>1 then
      AppendTo(output, ",");
    fi;
    AppendTo(output, "[");
    for iCol in [1..nbCol]
    do
      if iCol>1 then
        AppendTo(output, ",");
      fi;
      AppendTo(output, eMat[iLine][iCol]);
    od;
    AppendTo(output, "]");
  od;
  AppendTo(output, "])");
end;


PARI_PrintMatrix:=function(output, eMat)
  local nbLine, nbCol, iLine, iCol;
  nbLine:=Length(eMat);
  nbCol:=Length(eMat[1]);
  if nbLine=1 and nbCol=1 then
    AppendTo(output, "matrix(1,1,i,j,1)");
    return;
  fi;
  AppendTo(output, "[");
  for iLine in [1..nbLine]
  do
    if iLine>1 then
      AppendTo(output, ";");
    fi;
    for iCol in [1..nbCol]
    do
      if iCol>1 then
        AppendTo(output, ",");
      fi;
      AppendTo(output, eMat[iLine][iCol]);
    od;
  od;
  AppendTo(output, "]");
end;



LatexPrintInTab:=function(output, TabList, nbCol, NbSymPerItem)
  local pos, iCol, iLine, nbLine, remainder, u;
  AppendTo(output, "\\begin{tabular}{|");
  for iCol in [1..nbCol]
  do
    for u in [1..NbSymPerItem]
    do
      AppendTo(output, "c");
    od;
    AppendTo(output, "|");
  od;
  AppendTo(output, "}\n");
  AppendTo(output, "\\hline\n");
  remainder:=Length(TabList) mod nbCol;
  if remainder>0 then
    nbLine:=1+(Length(TabList)-remainder)/nbCol;
  else
    nbLine:=Length(TabList)/nbCol;
  fi;
  for iLine in [1..nbLine]
  do
    for iCol in [1..nbCol]
    do
      pos:=iCol+(iLine-1)*nbCol;
      if pos<=Length(TabList) then
        AppendTo(output, TabList[pos]);
      else
        AppendTo(output, "               ");
      fi;
      if iCol=nbCol then
        AppendTo(output, "\\\\\n");
      else
        AppendTo(output, "    &    ");
      fi;
    od;
  od;
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\end{tabular}\n");
end;




LatexPrintMatrix:=function(output, MatrixElt)
  local nbCol, nbLine, iCol, iLine, LineU;
  nbCol:=Length(MatrixElt[1]);
  nbLine:=Length(MatrixElt);
  AppendTo(output, "\\left(\\begin{array}{");
  for iCol in [1..nbCol]
  do
    AppendTo(output, "c");
  od;
  AppendTo(output, "}\n");
  for iLine in [1..nbLine]
  do
    LineU:=MatrixElt[iLine];
    for iCol in [1..nbCol]
    do
      AppendTo(output, LineU[iCol]);
      if iCol < nbCol then
        AppendTo(output, " & ");
      fi;
    od;
    if iLine<nbLine then
      AppendTo(output, "\\\\");
    fi;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "\\end{array}\\right)\n");
end;


LatexPrintMatrixEqua:=function(output, MatrixElt)
  AppendTo(output, "\\begin{equation*}\n");
  LatexPrintMatrix(output, MatrixElt);
  AppendTo(output, "\\end{equation*}\n");
end;



PrintLatexFile:=function(output, TabList, nbCol)
  local nbObj, quot, nbLine, nbIntCol, LC, iC, i, iLine, ListString, eStrSmall, eStrEmpty, iCol, nbRemain, ListSmallString, GetSmallString, nbTot, iObj;
  nbObj:=Length(TabList);
  quot:=QuoInt(nbObj,nbCol);
  if quot=nbObj/nbCol then
    nbLine:=quot;
  else
    nbLine:=quot+1;
  fi;
  Print("nbObj=", nbObj, " nbCol=", nbCol, "  nbLine=", nbLine, " quot=", quot, "\n");
  nbIntCol:=Length(TabList[1]);
  #
  AppendTo(output, "\\begin{equation*}\n");
  AppendTo(output, "\\begin{array}{|");
  LC:="|";
  for iC in [1..nbIntCol]
  do
    LC:=Concatenation(LC, "c|");
  od;
  for i in [1..nbCol]
  do
    AppendTo(output, LC);
  od;
  #
  GetSmallString:=function(eObj)
    local eStr, iS;
    eStr:="";
    for iS in [1..nbIntCol]
    do
      eStr:=Concatenation(eStr, eObj[iS]);
      if iS<nbIntCol then
        eStr:=Concatenation(eStr, " & ");
      fi;
    od;
    return eStr;
  end;
  AppendTo(output, "|}\n");
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\hline\n");
  ListString:=[];
  for iLine in [1..nbLine]
  do
    Add(ListString, "");
  od;
  iCol:=1;
  iLine:=0;
  ListSmallString:=[];
  for iObj in [1..nbObj]
  do
    eStrSmall:=GetSmallString(TabList[iObj]);
    Add(ListSmallString, eStrSmall);
  od;
  nbRemain:=nbLine*nbCol - nbObj;
  eStrEmpty:=" ";
  for i in [2..nbIntCol]
  do
    eStrEmpty:=Concatenation(eStrEmpty, "& ");
  od;
  for i in [1..nbRemain]
  do
    Add(ListSmallString, eStrEmpty);
  od;
#  Print("ListSmallString=", ListSmallString, "\n");
  nbTot:=nbLine*nbCol;
  for iObj in [1..nbTot]
  do
    if iLine < nbLine then
      iLine:=iLine+1;
    else
      if iCol < nbCol then
        iCol:=iCol+1;
        iLine:=1;
      else
        Error("We are trapped in the matrix");
      fi;
    fi;
    Print("iObj=", iObj, " iCol=", iCol, " iLine=", iLine, "\n");
    eStrSmall:=ListSmallString[iObj];
    ListString[iLine]:=Concatenation(ListString[iLine], eStrSmall);
    if iCol < nbCol then
      ListString[iLine]:=Concatenation(ListString[iLine], " &");
    else
      ListString[iLine]:=Concatenation(ListString[iLine], "\\\\\n");
    fi;
  od;
  for iLine in [1..nbLine]
  do
    AppendTo(output, ListString[iLine]);
  od;
  AppendTo(output, "\\end{array}\n");
  AppendTo(output, "\\end{equation*}\n");
end;





PrintLatexFileHeader:=function(output, TabList, nbCol, HeaderPart)
  local nbObj, quot, nbLine, nbIntCol, LC, iC, i, iLine, ListString, eStrSmall, eStrEmpty, iCol, nbRemain, ListSmallString, GetSmallString, nbTot, iObj;
  nbObj:=Length(TabList);
  quot:=QuoInt(nbObj,nbCol);
  if quot=nbObj/nbCol then
    nbLine:=quot;
  else
    nbLine:=quot+1;
  fi;
  Print("nbObj=", nbObj, " nbCol=", nbCol, "  nbLine=", nbLine, " quot=", quot, "\n");
  nbIntCol:=Length(TabList[1]);
  #
  AppendTo(output, "\\begin{equation*}\n");
  AppendTo(output, "\\begin{array}{|");
  LC:="|";
  for iC in [1..nbIntCol]
  do
    LC:=Concatenation(LC, "c|");
  od;
  for i in [1..nbCol]
  do
    AppendTo(output, LC);
  od;
  #
  GetSmallString:=function(eObj)
    local eStr, iS;
    eStr:="";
    for iS in [1..nbIntCol]
    do
      eStr:=Concatenation(eStr, eObj[iS]);
      if iS<nbIntCol then
        eStr:=Concatenation(eStr, " & ");
      fi;
    od;
    return eStr;
  end;
  AppendTo(output, "|}\n");
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\hline\n");
  for iCol in [1..nbCol]
  do
    AppendTo(output, HeaderPart);
    if iCol < nbCol then
      AppendTo(output, " & ");
    fi;
  od;
  AppendTo(output, "\\\\\n");
  AppendTo(output, "\\hline\n");
  AppendTo(output, "\\hline\n");
  ListString:=[];
  for iLine in [1..nbLine]
  do
    Add(ListString, "");
  od;
  iCol:=1;
  iLine:=0;
  ListSmallString:=[];
  for iObj in [1..nbObj]
  do
    eStrSmall:=GetSmallString(TabList[iObj]);
    Add(ListSmallString, eStrSmall);
  od;
  nbRemain:=nbLine*nbCol - nbObj;
  eStrEmpty:=" ";
  for i in [2..nbIntCol]
  do
    eStrEmpty:=Concatenation(eStrEmpty, "& ");
  od;
  for i in [1..nbRemain]
  do
    Add(ListSmallString, eStrEmpty);
  od;
#  Print("ListSmallString=", ListSmallString, "\n");
  nbTot:=nbLine*nbCol;
  for iObj in [1..nbTot]
  do
    if iLine < nbLine then
      iLine:=iLine+1;
    else
      if iCol < nbCol then
        iCol:=iCol+1;
        iLine:=1;
      else
        Error("We are trapped in the matrix");
      fi;
    fi;
    Print("iObj=", iObj, " iCol=", iCol, " iLine=", iLine, "\n");
    eStrSmall:=ListSmallString[iObj];
    ListString[iLine]:=Concatenation(ListString[iLine], eStrSmall);
    if iCol < nbCol then
      ListString[iLine]:=Concatenation(ListString[iLine], " &");
    else
      ListString[iLine]:=Concatenation(ListString[iLine], "\\\\\n");
    fi;
  od;
  for iLine in [1..nbLine]
  do
    WriteAll(output, ListString[iLine]);
  od;
  AppendTo(output, "\\end{array}\n");
  AppendTo(output, "\\end{equation*}\n");
end;





GetVectorAsString:=function(eIneq)
  local n, eStrIneq, i;
  n:=Length(eIneq);
  eStrIneq:="(";
  for i in [1..n]
  do
    if i>1 then
      eStrIneq:=Concatenation(eStrIneq, ",");
    fi;
    eStrIneq:=Concatenation(eStrIneq, String(eIneq[i]));
  od;
  eStrIneq:=Concatenation(eStrIneq, ")");
  return eStrIneq;
end;




PrintStabChain:=function(eG)
  local eRec, iLev;
  eRec:=StabChain(eG);
  iLev:=0;
  while(true)
  do
    Print("iLev=", iLev, "\n");
    if IsBound(eRec.transversal)=false then
      break;
    fi;
    Print("  transversal=", eRec.transversal, "\n");
    Print("  orbit=", eRec.orbit, "\n");
    Print("  genlabels=", eRec.genlabels, "\n");
    if IsBound(eRec.stabilizer) then
      eRec:=eRec.stabilizer;
    else
      break;
    fi;
    iLev:=iLev+1;
  od;
end;



# File must be of the form path/file_pre.tex
# The footer and header are added
# to form the path/file.tex
# and the compilation is done with latex/dvips/ps2pdf
LATEX_Compilation:=function(eFile)
  local FinalFileTex, FinalFileDVI, FinalFileTexB, FinalFileDVIB, FinalFilePSB, eDirTEX, eFileFoot, eFileHead, eSplit, LastStr, lenLast, eFileRed, eSuffix, posSlash, eDir;
  eSplit:=STRING_Split(eFile, "/");
  LastStr:=eSplit.ListStrInter[Length(eSplit.ListStrInter)];
  lenLast:=Length(LastStr);
  eFileRed:=LastStr{[1..lenLast-8]};
  eSuffix:=LastStr{[lenLast-7..lenLast]};
  if eSuffix<>"_pre.tex" then
    Print("eFile=", eFile, "\n");
    Print("LastStr=", LastStr, "\n");
    Error("Last characters of LastStr should be _pre.tex");
  fi;
  posSlash:=eSplit.ListMatch[Length(eSplit.ListMatch)];
  eDir:=eFile{[1..posSlash]};
  FinalFileTex:=Concatenation(eDir, "/", eFileRed, ".tex");
  FinalFileDVI:=Concatenation(eDir, "/", eFileRed, ".dvi");
  FinalFileTexB:=Concatenation(eFileRed, ".tex");
  FinalFileDVIB:=Concatenation(eFileRed, ".dvi");
  FinalFilePSB:=Concatenation(eFileRed, ".ps");
  eDirTEX:=DirectoriesPackageLibrary("gapcommon", "DATA/TEX")[1];
  eFileFoot:=Filename(eDirTEX, "Footer.tex");
  eFileHead:=Filename(eDirTEX, "Header.tex");
  Exec("cat ", eFileHead, " ", eFile, " ", eFileFoot, " > ", FinalFileTex);
  Exec("(cd ", eDir, " && latex ", FinalFileTexB, ")");
  Exec("(cd ", eDir, " && dvips ", FinalFileDVIB, " -o )");
  Exec("(cd ", eDir, " && ps2pdf ", FinalFilePSB, ")");
end;


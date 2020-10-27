FileZsolve:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"zsolve");
FileIntPoints:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"POLY_IntegralPoints");



GetIntegralPointsIteration_Kernel:=function(FAC, EXT)
  local FileFAC, FileEXT, FileOUT, ListPoint, TheCommand;
  FileFAC:=Filename(POLYHEDRAL_tmpdir,"Iter.FAC");
  FileEXT:=Filename(POLYHEDRAL_tmpdir,"Iter.EXT");
  FileOUT:=Filename(POLYHEDRAL_tmpdir,"Iter.OUT");
  RemoveFileIfExist(FileFAC);
  RemoveFileIfExist(FileEXT);
  RemoveFileIfExist(FileOUT);
  SYMPOL_PrintMatrix(FileFAC, FAC);
  SYMPOL_PrintMatrix(FileEXT, EXT);
  #
  TheCommand:=Concatenation(FileIntPoints, " ", FileFAC, " ", FileEXT, " ", FileOUT);
  Exec(TheCommand);
  #
  ListPoint:=ReadAsFunction(FileOUT)();
  RemoveFile(FileFAC);
  RemoveFile(FileEXT);
  RemoveFile(FileOUT);
  return ListPoint;
end;

GetIntegralPointsIteration:=function(FAC)
  local EXT, n, ListPointsEXT, ListPoints;
  EXT:=DualDescription(FAC);
  n:=Length(FAC[1])-1;
  ListPointsEXT:=GetIntegralPointsIteration_Kernel(FAC, EXT);
  ListPoints:=List(ListPointsEXT, x->x{[2..n+1]});
  return ListPoints;
end;




MyWriteVector:=function(output, eLine)
  local eEnt;
  for eEnt in eLine
  do
    AppendTo(output, eEnt, " ");
  od;
  AppendTo(output, "\n");
end;

#
#
# The polytope is given by FAC with the right hand
# side on first coordinate.
RunZsolve:=function(FACin)
  local FAC, FileFac, FilePre, FileMat, FileRel, FileRhs, FileSgn, FileLog, FileHom, FileInh, FileHomTail, FileInhTail, p, nbIneq, FACred, eLineRhs, output, i, TheCommand, TheHOM, TheINH, eLine;
  FAC:=List(FACin, RemoveFraction);
  FileFac:=Filename(POLYHEDRAL_tmpdir,"PROJECT.fac");
  FilePre:=Filename(POLYHEDRAL_tmpdir,"PROJECT");
  FileMat:=Filename(POLYHEDRAL_tmpdir,"PROJECT.mat");
  FileRel:=Filename(POLYHEDRAL_tmpdir,"PROJECT.rel");
  FileRhs:=Filename(POLYHEDRAL_tmpdir,"PROJECT.rhs");
  FileSgn:=Filename(POLYHEDRAL_tmpdir,"PROJECT.sign");
  FileHom:=Filename(POLYHEDRAL_tmpdir,"PROJECT.zhom");
  FileInh:=Filename(POLYHEDRAL_tmpdir,"PROJECT.zinhom");
  FileHomTail:=Filename(POLYHEDRAL_tmpdir,"PROJECT.zhom_tail");
  FileInhTail:=Filename(POLYHEDRAL_tmpdir,"PROJECT.zinhom_tail");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"PROJECT.log");
  p:=Length(FAC[1]);
  FACred:=List(FAC, x->x{[2..p]});
  nbIneq:=Length(FAC);
  eLineRhs:=List(FAC, x->-x[1]);
  #
  SaveDataToFile(FileFac, FAC);
#  Print("FileFac = ", FileFac, "\n");
  #
  output:=OutputTextFile(FileMat, true);
  AppendTo(output, nbIneq, " ", p-1, "\n");
  for eLine in FACred
  do
    MyWriteVector(output, eLine);
  od;
  CloseStream(output);
  #
  output:=OutputTextFile(FileRel, true);
  AppendTo(output, "1 ", nbIneq, "\n");
  for i in [1..nbIneq]
  do
    AppendTo(output, "> ");
  od;
  AppendTo(output, "\n");
  CloseStream(output);
  #
  output:=OutputTextFile(FileRhs, true);
  AppendTo(output, "1 ", nbIneq, "\n");
  MyWriteVector(output, eLineRhs);
  CloseStream(output);
  #
  output:=OutputTextFile(FileSgn, true);
  AppendTo(output, "1 ", p-1, "\n");
  for i in [1..p-1]
  do
    AppendTo(output, "0 ");
  od;
  AppendTo(output, "\n");
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileZsolve, " ", FilePre, " > ", FileLog);
#  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
  #
  if IsExistingFile(FileHom)=false or IsExistingFile(FileInh)=false then
    Print("The run of zsolve was apparentily not correct\n");
    Error("Please debug");
  fi;
  TheCommand:=Concatenation("cat ", FileHom, " | tail -n +2 > ", FileHomTail);
#  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
  #
  TheCommand:=Concatenation("cat ", FileInh, " | tail -n +2 > ", FileInhTail);
#  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
  #
  TheHOM:=ReadVectorFile(FileHomTail);
  TheINH:=ReadVectorFile(FileInhTail);
  #
  RemoveFileIfExist(FileMat);
  RemoveFileIfExist(FileRel);
  RemoveFileIfExist(FileRhs);
  RemoveFileIfExist(FileSgn);
  RemoveFileIfExist(FileHom);
  RemoveFileIfExist(FileInh);
  RemoveFileIfExist(FileLog);
  RemoveFileIfExist(FileHomTail);
  RemoveFileIfExist(FileInhTail);
  if First(TheINH, x->Length(x)<>p-1)<>fail then
    Error("Inconsistent vector length in TheINH");
  fi;
  if First(TheHOM, x->Length(x)<>p-1)<>fail then
    Error("Inconsistent vector length in TheHOM");
  fi;
  return rec(TheHOM:=TheHOM, TheINH:=TheINH);
end;



GetIntegralPointsZsolve:=function(FAC)
  local n, FACred, TheResult;
  n:=Length(FAC[1])-1;
  FACred:=RemoveRedundancy(FAC);
  TheResult:=RunZsolve(FACred);
  Print("|TheResult.TheHOM|=", Length(TheResult.TheHOM), "\n");
  Print("|TheResult.TheINH|=", Length(TheResult.TheINH), "\n");
  if Position(TheResult.TheINH, ListWithIdenticalEntries(n,0))=fail then
    Error("Major errror to be solved");
  fi;
  if Length(TheResult.TheHOM)>0 then
    Error("We should not have any homogeneous solutions");
  fi;
  return TheResult.TheINH;
end;






FindIntegralsolutions_Exhaustive:=function(RecMatrix, TheOpt)
  local nbRow, nbCol, ListPartSol, ListSol, NewListPartSol, ePartSol, eDiff, iRow, IsFeasible, vDiff, nPartSol;
  nbRow:=Length(RecMatrix.TheMat);
  nbCol:=Length(RecMatrix.TheMat[1]);
  if Length(RecMatrix.eVect)<>nbCol then
    Print("We have nbCol=", nbCol, "\n");
    Print("|eVect|=", Length(RecMatrix.eVect), "\n");
    Error("Inconsistency in input");
  fi;
  ListPartSol:=[ListWithIdenticalEntries(nbRow,0)];
  ListSol:=[];
  while(true)
  do
    NewListPartSol:=[];
    for ePartSol in ListPartSol
    do
      eDiff:=RecMatrix.eVect - ePartSol*RecMatrix.TheMat;
      for iRow in [1..nbRow]
      do
        if TheOpt="integer" then
          IsFeasible:=true;
        else
          IsFeasible:=ePartSol[iRow]=0;
        fi;
        if IsFeasible then
          vDiff:=eDiff - RecMatrix.TheMat[iRow];
          if First(vDiff, x->x<0)=fail then
            nPartSol:=List(ePartSol, x->x);
            nPartSol[iRow]:=nPartSol[iRow] + 1;
            if First(vDiff, x->x>0)=fail then
              Add(ListSol, nPartSol);
            else
              Add(NewListPartSol, nPartSol);
            fi;
          fi;
        fi;
      od;
    od;
    ListPartSol:=Set(NewListPartSol);
    Print("|ListPartSol|=", Length(ListPartSol), "\n");
    if Length(ListPartSol)=0 then
      break;
    fi;
  od;
  return ListSol;
end;


FindIntegralsolutions_Zsolve:=function(RecMatrix, TheOpt)
  local eSolInt, NSP, dimNSP, nbRow, nbCol, ListIneq, iRow, eIneq, fIneq, iNSP, eRecSolve, ListSol, eSol, TheX;
  eSolInt:=SolutionIntMat(RecMatrix.TheMat, RecMatrix.eVect);
  if eSolInt=fail then
    return [];
  fi;
  NSP:=NullspaceIntMat(RecMatrix.TheMat);
  dimNSP:=Length(NSP);
  nbRow:=Length(RecMatrix.TheMat);
  nbCol:=Length(RecMatrix.TheMat[1]);
  if Length(RecMatrix.eVect)<>nbCol then
    Print("We have nbCol=", nbCol, "\n");
    Print("|eVect|=", Length(RecMatrix.eVect), "\n");
    Error("Inconsistency in input");
  fi;
  Print("nbRow=", nbRow, " nbCol=", nbCol, " dimNSP=", dimNSP, "\n");
  ListIneq:=[];
  for iRow in [1..nbRow]
  do
    eIneq:=ListWithIdenticalEntries(dimNSP+1, 0);
    fIneq:=ListWithIdenticalEntries(dimNSP+1, 0);
    eIneq[1]:=eSolInt[iRow];
    fIneq[1]:=1 - eSolInt[iRow];
    for iNSP in [1..dimNSP]
    do
      eIneq[iNSP+1]:=NSP[iNSP][iRow];
      fIneq[iNSP+1]:=-NSP[iNSP][iRow];
    od;
    Add(ListIneq, eIneq);
    if TheOpt="binary" then
      Add(ListIneq, fIneq);
    fi;
  od;
  Print("|ListIneq|=", Length(ListIneq), "\n");
  eRecSolve:=RunZsolve(ListIneq);
  ListSol:=[];
  for eSol in eRecSolve.TheINH
  do
    TheX:=eSolInt + eSol*NSP;
    Add(ListSol, TheX);
  od;
  return ListSol;
end;






Kernel_FindIntegralsolutions_Libexact:=function(RecMatrix, TheOpt)
  local nbRow, nbCol, VectXcond, VectYcond, ListSol, ListVectSol, eSol, eVect;
  if TheOpt<>"binary" then
    Error("Right now libexact strategy works only if the variable is binary. Could work if we have an upper bound on the value though");
  fi;
  nbRow:=Length(RecMatrix.TheMat);
  nbCol:=Length(RecMatrix.TheMat[1]);
  if Length(RecMatrix.eVect)<>nbCol then
    Print("We have nbCol=", nbCol, "\n");
    Print("|eVect|=", Length(RecMatrix.eVect), "\n");
    Error("Inconsistency in input");
  fi;
  VectXcond:=ListWithIdenticalEntries(nbRow,1);
  VectYcond:=RecMatrix.eVect;
  ListSol:=EnumerateLibexactSolution(RecMatrix.TheMat, VectXcond, VectYcond);
  ListVectSol:=[];
  for eSol in ListSol
  do
    eVect:=ListWithIdenticalEntries(nbRow,0);
    eVect{eSol}:=ListWithIdenticalEntries(Length(eSol), 1);
    Add(ListVectSol, eVect);
  od;
  return ListVectSol;
end;


FindIntegralsolutions_Libexact:=function(RecMatrix, TheOpt)
  local nbRow, nbCol, ListZero, ListPlus, ListStatus, TheMatRed, iRow, eSum, eStatus, ListRowSelect, eVectRed, RecMatrixRed, ListSolRed, ListSol, eSol, eSolRed;
  nbRow:=Length(RecMatrix.TheMat);
  nbCol:=Length(RecMatrix.TheMat[1]);
  if Length(RecMatrix.eVect)<>nbCol then
    Print("We have nbCol=", nbCol, "\n");
    Print("|eVect|=", Length(RecMatrix.eVect), "\n");
    Error("Inconsistency in input");
  fi;
  ListZero:=Filtered([1..nbCol], x->RecMatrix.eVect[x]=0);
  ListPlus:=Filtered([1..nbCol], x->RecMatrix.eVect[x]>0);
  ListStatus:=[];
  TheMatRed:=[];
  for iRow in [1..nbRow]
  do
    eSum:=Sum(RecMatrix.TheMat[iRow]{ListZero});
    if eSum>0 then
      eStatus:=0;
    else
      eStatus:=1;
    fi;
    Add(ListStatus, eStatus);
    if eStatus=1 then
      Add(TheMatRed, RecMatrix.TheMat[iRow]{ListPlus});
    fi;
  od;
  ListRowSelect:=Filtered([1..nbRow], x->ListStatus[x]=1);
#  Print("ListRowSelect=", ListRowSelect, "\n");
  eVectRed:=RecMatrix.eVect{ListPlus};
  RecMatrixRed:=rec(TheMat:=TheMatRed, eVect:=eVectRed);
  ListSolRed:=Kernel_FindIntegralsolutions_Libexact(RecMatrixRed, TheOpt);
#  Error("Debug from here");
  ListSol:=[];
  for eSolRed in ListSolRed
  do
    eSol:=ListWithIdenticalEntries(nbRow,0);
    eSol{ListRowSelect}:=eSolRed;
    if eSol*RecMatrix.TheMat<>RecMatrix.eVect then
      Error("Inconsistency in solutioning");
    fi;
    Add(ListSol, eSol);
  od;
  return ListSol;
end;




#
# Find the integer solutions of the equation 
# v = x A with x an integer.
# two possibilities for TheOpt:
#  integer: x>= 0
#  binary : x=0 or 1
FindIntegralsolutions:=function(RecMatrix, TheOpt)
  local nbRow, nbCol, ListSol1, ListSol2, ListSol3, DoCheck;
  nbRow:=Length(RecMatrix.TheMat);
  nbCol:=Length(RecMatrix.TheMat[1]);
  if TheOpt<>"binary" and TheOpt<>"integer" then
    Error("TheOpt should be binary or integer");
  fi;
  if SolutionIntMat(RecMatrix.TheMat, RecMatrix.eVect)=fail then
    return [];
  fi;
  DoCheck:=false;
  if DoCheck=true then
    ListSol3:=FindIntegralsolutions_Libexact(RecMatrix, TheOpt);
    ListSol1:=FindIntegralsolutions_Exhaustive(RecMatrix, TheOpt);
    ListSol2:=FindIntegralsolutions_Zsolve(RecMatrix, TheOpt);
    if Set(ListSol1)<>Set(ListSol2) or Set(ListSol1)<>Set(ListSol3) then
      Print("|ListSol1|=", Length(ListSol1), "\n");
      Print("|ListSol2|=", Length(ListSol2), "\n");
      Print("|ListSol3|=", Length(ListSol3), "\n");
      Error("Clear bug that needs to be solved");
    fi;
  fi;
  if TheOpt="binary" then
    return FindIntegralsolutions_Libexact(RecMatrix, TheOpt);
  fi;
  return FindIntegralsolutions_Exhaustive(RecMatrix, TheOpt);
end;




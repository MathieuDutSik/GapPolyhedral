Filelpcddcleaner:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"lpcddcleaner");
FilelpcddcleanerPol:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"lpcddcleanerPol");
FileRedcheck:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"redcheck_gmp");
FileTestlp2:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"testlp2_gmp");
FileRedcheckRead:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"redcheckRead");
FileAdjacency:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"adjacency_gmp");
FileAdjacencyRead:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"adjacencyRead");
FileGlpsol:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"glpsol");
FileLpsolve:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"lp_solve");
FilePolyRedundancy:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"POLY_redundancy");
FilePolyRedundancyClarkson:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"POLY_redundancyClarkson");
FileLpsolveExtractSolution:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"LPSOLVE_ExtractSolution");
FileGLPSOL_ExtractXsol:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"GLPSOL_ExtractXsol");
FileStandaloneSparseSolver:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"StandaloneSparseSolver");
FileStandaloneSparseSolver_NNZ:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"StandaloneSparseSolver_NNZ");


CPP_RedundancyReduction:=function(EXT)
  local FileExt, FileOut, output, TheCommand, TheRet;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Redund.ext");
  FileOut:=Filename(POLYHEDRAL_tmpdir,"Redund.out");
  #
  output:=OutputTextFile(FileExt, true);;
  CPP_WriteMatrix(output, EXT);
  CloseStream(output);
  #
  TheCommand:=Concatenation(FilePolyRedundancy, " ", FileExt, " ", FileOut);
  Exec(TheCommand);
  #
  TheRet:=ReadAsFunction(FileOut)();
  RemoveFile(FileExt);
  RemoveFile(FileOut);
  return TheRet;
end;


CPP_RedundancyReductionClarkson:=function(EXT)
  local FileExt, FileOut, output, TheCommand, TheRet;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Redund.ext");
  FileOut:=Filename(POLYHEDRAL_tmpdir,"Redund.out");
  #
  output:=OutputTextFile(FileExt, true);;
  CPP_WriteMatrix(output, EXT);
  CloseStream(output);
  #
  Print(NullMat(5));
  TheCommand:=Concatenation(FilePolyRedundancyClarkson, " ", FileExt, " ", FileOut);
  Exec(TheCommand);
  #
  TheRet:=ReadAsFunction(FileOut)();
  RemoveFile(FileExt);
  RemoveFile(FileOut);
  return TheRet;
end;




AdjacencyComputation:=function(EXT)
  local FileExt, FileError, FileRed, FileRead, output, TheRet;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Desc.ext");
  FileError:=Filename(POLYHEDRAL_tmpdir,"Desc.error");
  FileRed:=Filename(POLYHEDRAL_tmpdir,"Desc.redcheck");
  FileRead:=Filename(POLYHEDRAL_tmpdir,"Desc.read");
  #
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileAdjacency, " ", FileExt, " 2> ", FileError, " > ", FileRed);
  Exec(FileAdjacencyRead, " ", FileRed," > ", FileRead);
  TheRet:=ReadAsFunction(FileRead)();
  RemoveFile(FileExt);
  RemoveFile(FileError);
  RemoveFile(FileRed);  RemoveFile(FileRead);
  return TheRet;
end;



RedundancyCheckOriginal_QN:=function(Nval, EXT)
  local FileExt, FileError, FileRed, FileRead, output, TheRet, eEXT, NvalueFile;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Desc.ext");
  FileError:=Filename(POLYHEDRAL_tmpdir,"Desc.error");
  FileRed:=Filename(POLYHEDRAL_tmpdir,"Desc.redcheck");
  FileRead:=Filename(POLYHEDRAL_tmpdir,"Desc.read");
  RemoveFileIfExist(FileExt);
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  for eEXT in EXT
  do
    QN_WriteVector(Nval, output, eEXT);
  od;
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  NvalueFile:="/tmp/InitialN";
  RemoveFileIfExist(NvalueFile);
  output:=OutputTextFile(NvalueFile, true);;
  AppendTo(output, " ", Nval, "\n");
  CloseStream(output);
  #
  Exec(FileRedcheck_QN, " ", FileExt, " 2> ", FileError, " > ", FileRed);
  Exec(FileRedcheckRead, " ", FileRed," > ", FileRead);
  TheRet:=ReadAsFunction(FileRead)();
  RemoveFile(FileExt);
  RemoveFile(FileError);
  RemoveFile(FileRed);
  RemoveFile(FileRead);
  return Difference([1..Length(EXT)], TheRet);
end;



RedundancyCheckOriginal_Rational:=function(EXTinp)
  local EXT, FileExt, FileError, FileRed, FileRead, output, TheRet;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Desc.ext");
  FileError:=Filename(POLYHEDRAL_tmpdir,"Desc.error");
  FileRed:=Filename(POLYHEDRAL_tmpdir,"Desc.redcheck");
  FileRead:=Filename(POLYHEDRAL_tmpdir,"Desc.read");
  EXT:=RemoveFractionMatrix(EXTinp);
  RemoveFileIfExist(FileExt);
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileRedcheck, " ", FileExt, " 2> ", FileError, " > ", FileRed);
  Exec(FileRedcheckRead, " ", FileRed," > ", FileRead);
  TheRet:=ReadAsFunction(FileRead)();
  RemoveFile(FileExt);
  RemoveFile(FileError);
  RemoveFile(FileRed);
  RemoveFile(FileRead);
  return Difference([1..Length(EXT)], TheRet);
end;



RedundancyCheckOriginal:=function(EXT)
  local Nval;
  if IsMatrixRational(EXT)=true then
    return RedundancyCheckOriginal_Rational(EXT);
  fi;
  for Nval in [2,5]
  do
    if QN_IsMatrix(Nval, EXT)=true then
      return RedundancyCheckOriginal_QN(Nval, EXT);
    fi;
  od;
  Error("You have to build your own arithmetic");
end;



RedundancyCheck:=function(EXT)
  local ListPos1, ListPos2;
  ListPos1:=Filtered([1..Length(EXT)], x->EXT[x]*EXT[x]>0);
  ListPos2:=RedundancyCheckOriginal(EXT{ListPos1});
  return ListPos1{ListPos2};
end;



LinearProgramming_QN:=function(Nval, InequalitySet, ToBeMinimized)
  local FileIne, FileLps, FileErr, FileGap, FileDdl, FileLog, outputCdd, input, eLine, A, TheDim, eVect, eIneq, eSum, eEnt, absVal, NvalueFile, output;
  FileIne:=Filename(POLYHEDRAL_tmpdir, "LP_QN.ine");
  FileLps:=Filename(POLYHEDRAL_tmpdir, "LP_QN.lps");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "LP_QN.error");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "LP_QN.gap");
  FileDdl:=Filename(POLYHEDRAL_tmpdir, "LP_QN.ddl");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "LP_QN.log");
#  Print("FileIne=", FileIne, "\n");
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLps);
  RemoveFileIfExist(FileErr);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileDdl);
  RemoveFileIfExist(FileLog);
  TheDim:=Length(InequalitySet[1]);
  for eVect in InequalitySet
  do
    if Length(eVect)<>TheDim then
      Print("Incoherence in dimensions of InequalitySet\n");
      Error("Please correct");
    fi;
  od;
  if TheDim<>Length(ToBeMinimized) then
    Error("Incoherence in dimensions, please be careful");
  fi;
  outputCdd:=OutputTextFile(FileIne, true);;
  AppendTo(outputCdd, "H-representation\n");
  AppendTo(outputCdd, "begin\n");
  AppendTo(outputCdd, " ", Length(InequalitySet), " ", Length(ToBeMinimized), " integer\n");
  for eIneq in InequalitySet
  do
    QN_WriteVector(Nval, outputCdd, eIneq);
  od;
  AppendTo(outputCdd, "end\n");
  AppendTo(outputCdd, "minimize\n");
  QN_WriteVector(Nval, outputCdd, ToBeMinimized);
  CloseStream(outputCdd);
  #
  NvalueFile:="/tmp/InitialN";
  RemoveFileIfExist(NvalueFile);
  output:=OutputTextFile(NvalueFile, true);;
  AppendTo(output, " ", Nval, "\n");
  CloseStream(output);
  #
  Exec(FileTestlp2_QN, " ", FileIne, " 2> ", FileErr, " > ", FileLog);
  Exec(FilelpcddcleanerQN, " ", String(Nval), " < ", FileLog, " > ", FileGap);
  A:=ReadAsFunction(FileGap)();
  if IsBound(A.dual_direction) then
    eSum:=ListWithIdenticalEntries(TheDim,0);
    for eEnt in A.dual_direction
    do
      if QN_IsPositive(Nval, eEnt[2]) then
        absVal:=eEnt[2];
      else
        absVal:=-eEnt[2];
      fi;
      eSum:=eSum+InequalitySet[eEnt[1]]*absVal;
    od;
    if QN_IsNonNegative(Nval,eSum[1])=true then
      Print("Apparently something is not understood for\n");
      Error("cdd and linear programming (unfeasibilities) 1");
    fi;
    if eSum{[2..TheDim]}<>ListWithIdenticalEntries(TheDim-1,0) then
      Print("Apparently something is not understood for\n");
      Error("cdd and linear programming (unfeasibilities) 2");
    fi;
  fi;
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLps);
  RemoveFileIfExist(FileErr);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileDdl);
  RemoveFileIfExist(FileLog);
  return A;
end;



#
# this thing is the end of a long design road.
# realizing that linear programming is quite complex.
# Basically, everything is outputed, everything is read
# and you have to make interpretations yourself.
LinearProgramming_Rational:=function(InequalitySet, ToBeMinimized)
  local FileIne, FileLps, FileErr, FileGap, FileDdl, FileLog, outputCdd, input, eLine, TheLP, TheDim, eVect, eSum, eEnt, nbIneq, TheCommand1, TheCommand2;
  FileIne:=Filename(POLYHEDRAL_tmpdir, "LP.ine");
  FileLps:=Filename(POLYHEDRAL_tmpdir, "LP.lps");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "LP.error");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "LP.gap");
  FileDdl:=Filename(POLYHEDRAL_tmpdir, "LP.ddl");
  FileLog:=Filename(POLYHEDRAL_tmpdir, "LP.log");
#  Print("FileIne=", FileIne, "\n");
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLps);
  RemoveFileIfExist(FileErr);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileDdl);
  RemoveFileIfExist(FileLog);
  TheDim:=Length(InequalitySet[1]);
  nbIneq:=Length(InequalitySet);
#  Print("nbIneq=", nbIneq, "  TheDim=", TheDim, "\n");
  for eVect in InequalitySet
  do
    if Length(eVect)<>TheDim then
      Print("Incoherence in dimensions of InequalitySet, please");
      Error("Please correct");
    fi;
  od;
  if TheDim<>Length(ToBeMinimized) then
    Error("Incoherence in dimensions, please be careful");
  fi;
  outputCdd:=OutputTextFile(FileIne, true);;
  AppendTo(outputCdd, "H-representation\n");
  AppendTo(outputCdd, "begin\n");
  AppendTo(outputCdd, " ", Length(InequalitySet), " ", Length(ToBeMinimized), " integer\n");
  WriteMatrix(outputCdd, InequalitySet);
  AppendTo(outputCdd, "end\n");
  AppendTo(outputCdd, "minimize\n");
  WriteVector(outputCdd, ToBeMinimized);
  CloseStream(outputCdd);
  #
  TheCommand1:=Concatenation(FileTestlp2, " ", FileIne, " 2> ", FileErr, " > ", FileLog);
#  Print("TheCommand1=", TheCommand1, "\n");
  Exec(TheCommand1);
  #
  TheCommand2:=Concatenation(Filelpcddcleaner, " < ", FileLog, " > ", FileGap);
#  Print("TheCommand2=", TheCommand2, "\n");
  Exec(TheCommand2);
  #
  TheLP:=ReadAsFunction(FileGap)();
  TheLP.method:="cdd";
  if IsBound(TheLP.dual_direction) then
#    Print("TheLP.dual_direction=", TheLP.dual_direction, "\n");
    eSum:=ListWithIdenticalEntries(TheDim,0);
    for eEnt in TheLP.dual_direction
    do
#      Print("eIneq=", InequalitySet[eEnt[1]], "\n");
      eSum:=eSum+InequalitySet[eEnt[1]]*AbsInt(eEnt[2]);
    od;
    if eSum[1] >= 0 then
      Print("Apparently something is not understood for\n");
      Print("cdd and linear programming (unfeasibilities) 1\n");
      Error("Please correct");
    fi;
    if eSum{[2..TheDim]}<>ListWithIdenticalEntries(TheDim-1,0) then
      Print("Apparently something is not understood for\n");
      Print("cdd and linear programming (unfeasibilities) 2\n");
      Error("Please correct");
    fi;
  fi;
  if IsBound(TheLP.primal_solution) then
    eVect:=ListWithIdenticalEntries(TheDim-1,0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheLP.eVect:=eVect;
    TheLP.TheVert:=Concatenation([1], eVect);
  fi;
#  Print("Copy the files here\n");
#  Print(NullMat(5));
  RemoveFileIfExist(FileIne);
  RemoveFileIfExist(FileLps);
  RemoveFileIfExist(FileErr);
  RemoveFileIfExist(FileGap);
  RemoveFileIfExist(FileDdl);
  RemoveFileIfExist(FileLog);
  return TheLP;
end;



LinearProgramming_General_Code:=function(InequalitySet, ToBeMinimized)
  local Nval;
  if IsMatrixRational(InequalitySet) and IsVectorRational(ToBeMinimized) then
    return LinearProgramming_Rational(InequalitySet, ToBeMinimized);
  fi;
  for Nval in [2,5]
  do
    if QN_IsMatrix(Nval, InequalitySet) and QN_IsVector(Nval, ToBeMinimized) then
      return LinearProgramming_QN(Nval, InequalitySet, ToBeMinimized);
    fi;
  od;
  Error("You have to build your own arithmetic");
end;


LinearProgramming:=function(InequalitySet, ToBeMinimized)
  local Nval;
  if IsMatrixRational(InequalitySet) and IsVectorRational(ToBeMinimized) then
    return LinearProgramming_Rational(InequalitySet, ToBeMinimized);
  fi;
  Error("You have to build your own arithmetic or use LinearProgrammingGeneralCode");
end;



GetPolytopizationInfo:=function(FAC)
  local eSet, FACred, dimRed, ListIneq, ToBeMinimized, eFac, eIneq, TheLP, eVect, eEnt, eMatBig, eBasis, eMatTrans, NewListIneq, eProd, fIneq;
  eSet:=ColumnReduction(FAC).Select;
  FACred:=List(FAC, x->x{eSet});
  dimRed:=Length(eSet);
  ListIneq:=[];
  ToBeMinimized:=ListWithIdenticalEntries(1+dimRed,0);
  for eFac in FACred
  do
    eIneq:=Concatenation([-1], eFac);
    Add(ListIneq, eIneq);
    ToBeMinimized:=ToBeMinimized+eIneq;
  od;
  TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
  if IsBound(TheLP.primal_solution)=false then
    Error("Clear inconsistency, maybe the cone is empty");
  fi;
  eVect:=ListWithIdenticalEntries(dimRed,0);
  for eEnt in TheLP.primal_solution
  do
    eVect[eEnt[1]]:=eEnt[2];
  od;
  eMatBig:=Concatenation([eVect], IdentityMat(dimRed));
  eBasis:=RowReduction(eMatBig).EXT;
  eMatTrans:=TransposedMat(eBasis);
  return rec(eSet:=eSet, eMatTrans:=eMatTrans);
end;


DoPolytopization:=function(eRecPoly, FAC)
  local NewListIneq, FACred, eIneq, eProd, fIneq;
  NewListIneq:=[];
  FACred:=List(FAC, x->x{eRecPoly.eSet});
  for eIneq in FACred
  do
    eProd:=eIneq*eRecPoly.eMatTrans;
    fIneq:=eProd/eProd[1];
    Add(NewListIneq, fIneq);
  od;
  return NewListIneq;
end;



#
#
# This polytopization should be equivariant
# But unfortunately, it sometimes does not work.
DirectPolytopizationEXT:=function(PreEXT)
  local EXT, TheDim, TheSum, Qmat, eEXT, eProd, NSP, eBasis, eBasisInv, RetEXT, eSolB, eVal, eSolC;
  EXT:=ColumnReduction(PreEXT).EXT;
  TheDim:=Length(EXT[1]);
  TheSum:=ListWithIdenticalEntries(TheDim, 0);
  Qmat:=NullMat(TheDim,TheDim);
  for eEXT in EXT
  do
    TheSum:=TheSum + eEXT;
    Qmat:=Qmat + TransposedMat([eEXT])*[eEXT];
  od;
  eProd:=TheSum*Inverse(Qmat);
  NSP:=NullspaceMat(TransposedMat([eProd]));
  eBasis:=Concatenation([TheSum], NSP);
  eBasisInv:=Inverse(eBasis);
  RetEXT:=[];
  for eEXT in EXT
  do
    eSolB:=eEXT*eBasisInv;
    eVal:=eSolB[1];
    if eVal <= 0 then
      Error("We should have eVal>0");
    fi;
    eSolC:=eSolB / eVal;
    Add(RetEXT, eSolC);
  od;
  return RetEXT;
end;



PolytopizationGeneralCone:=function(FAC)
  local eRecPoly;
  eRecPoly:=GetPolytopizationInfo(FAC);
  return DoPolytopization(eRecPoly, FAC);
end;



OperationRemovalOfEquation:=function(EqualitySet)
  local TRSP, nRank, Irr, rank, pos, ListM, Diffe, Matri, iLin, Line, iCol, ListV, INVM, TE, ListExpr, ERL, FuncChange, FuncBack;
  TRSP:=TransposedMat(EqualitySet);
  nRank:=RankMat(EqualitySet);
  Irr:=[];
  rank:=0;
  pos:=2;
  ListM:=[];
  while (rank<nRank)
  do
    TE:=ShallowCopy(Irr);
    Add(TE, TRSP[pos]);
    if (RankMat(TE) > rank) then
      Irr:=ShallowCopy(TE);
      rank:=rank+1;
      Add(ListM, pos);
    fi;
    pos:=pos+1;
  od;
#  Print("ListM=", ListM, "\n");
  Diffe:=Difference([2..Length(TRSP)], ListM);
  Matri:=[];
  for iLin in [1..nRank]
  do
    Line:=[];
    for iCol in [1..nRank]
    do
      Add(Line, EqualitySet[iLin][ListM[iCol]]);
    od;
    Add(Matri, Line);
  od;
  ListV:=[];
  for iLin in [1..nRank]
  do
    Line:=[-EqualitySet[iLin][1]];
    for iCol in [1..Length(Diffe)]
    do
      Add(Line, -EqualitySet[iLin][Diffe[iCol]]);
    od;
    Add(ListV, Line);
  od;
  ListExpr:=[];
  for iLin in [1..Length(Diffe)]
  do
    Line:=ListWithIdenticalEntries(1+Length(Diffe), 0);
    Line[1+iLin]:=1;
    ListExpr[Diffe[iLin]]:=ShallowCopy(Line);
    Print("idx=", Diffe[iLin], "  eq=", Line, "\n");
  od;
  INVM:=Inverse(Matri);
  for iLin in [1..nRank]
  do
    ERL:=0;
    for iCol in [1..nRank]
    do
      ERL:=ERL+INVM[iLin][iCol]*ListV[iCol];
    od;
    ListExpr[ListM[iLin]]:=ERL;
    Print("idx=", ListM[iLin], "  eq=", ERL, "\n");
  od;
  FuncChange:=function(EV)
    local SU, i;
    SU:=ShallowCopy(ListWithIdenticalEntries(1+Length(Diffe), 0));
    SU[1]:=EV[1];
    for i in [2..Length(EV)]
    do
      SU:=SU+ListExpr[i]*EV[i];
    od;
    return SU;
  end;
  FuncBack:=function(SU)
    local NewVector;
    NewVector:=ShallowCopy(ListWithIdenticalEntries(Length(EqualitySet[1]), 0));
    NewVector[1]:=1;
    for iCol in [1..Length(Diffe)]
    do
      NewVector[Diffe[iCol]]:=SU[iCol+1];
    od;
    for iCol in [1..nRank]
    do
      NewVector[ListM[iCol]]:=ListV[iCol]*SU;
    od;
    return NewVector;
  end;
  return rec(FuncChange:=FuncChange, FuncBack:=FuncBack);
end;



LinearProgrammingPolytopeWithEquations:=function(EqualitySet, InequalitySet, ToBeMinimized)
  local LSFR, NewInequalitySet, eV, NewToBeMinimized, FuncChange, FuncBack, reply;
  LSFR:=OperationRemovalOfEquation(EqualitySet);
  FuncChange:=LSFR.FuncChange;
  FuncBack:=LSFR.FuncBack;
  NewInequalitySet:=[];
  for eV in InequalitySet
  do
    Add(NewInequalitySet, FuncChange(eV));
  od;
  NewToBeMinimized:=FuncChange(ToBeMinimized);
  reply:=LinearProgramming(NewInequalitySet, NewToBeMinimized);
  return rec(Vector:=FuncBack(reply.Vector), Value:=reply.Value);
end;



EliminationByRedundancyCone:=function(FAC, EXT)
  local dimSpace, ListIrred, eFac, ListIncd;
  dimSpace:=Length(FAC[1]);
  ListIrred:=[];
  for eFac in FAC
  do
    ListIncd:=Filtered(EXT, x->x*eFac=0);
    if PersoRankMat(ListIncd) = dimSpace-1 then
      Add(ListIrred, eFac);
    fi;
  od;
  return ListIrred;
end;



SearchNonExistencePositiveRelation:=function(ListVectRat, ListStatus)
  local ListVect, nbVect, TheDim, ListInequalities, iVect, H, iCol, ListIndexPos, TheSum, ToBeMinimized, TheLP, TheSolutionRed, eEnt, ListVectCoeff;
  ListVect:=RemoveFractionMatrix(ListVectRat);
  nbVect:=Length(ListVect);
  TheDim:=Length(ListVect[1]);
  ListInequalities:=[];
  for iVect in [1..nbVect]
  do
    H:=[0];
    for iCol in [1..TheDim]
    do
      Add(H, ListVect[iVect][iCol]);
    od;
    Add(ListInequalities, H);
  od;
  ListIndexPos:=Filtered([1..nbVect], x->ListStatus[x]=">0");
  if Length(ListIndexPos)=0 then
    Error("You are losing your time, vector 0 is just fine");
  fi;
  H:=[-1];
  for iCol in [1..TheDim]
  do
    TheSum:=0;
    for iVect in ListIndexPos
    do
      TheSum:=TheSum+ListVect[iVect][iCol];
    od;
    Add(H, TheSum);
  od;
  Add(ListInequalities, H);
  ToBeMinimized:=[0];
  for iCol in [1..TheDim]
  do
    TheSum:=0;
    for iVect in [1..nbVect]
    do
      TheSum:=TheSum+ListVect[iVect][iCol];
    od;
    Add(ToBeMinimized, TheSum);
  od;
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
  if IsBound(TheLP.primal_solution) then
    TheSolutionRed:=ListWithIdenticalEntries(TheDim, 0);
    for eEnt in TheLP.primal_solution
    do
      TheSolutionRed[eEnt[1]]:=eEnt[2];
    od;
    ListVectCoeff:=TheSolutionRed*TransposedMat(ListVectRat);
    for iVect in [1..nbVect]
    do
      if ListVectCoeff[iVect]< 0 then
        Error("We failed in proof of nonexistence case 1");
      fi;
    od;
    TheSum:=Sum(ListVectCoeff{ListIndexPos});
    if TheSum<=0 then
      Error("We failed in proof of nonexistence case 2");
    fi;
    return TheSolutionRed;
  else
    return false;
  fi;
end;



SearchPositiveRelation:=function(ListVect, TheConstraint)
  local ArithFct, NSP, nbVect, TheDim, nbRelation, ListInequalities, iVect, H, iRel, ToBeMinimized, TheLP, TheSolutionRed, TheSolution, TheCertif, TheProd, eEnt, SetVectorPos, eSet, TheSum;
  ArithFct:=GetArithmeticityMatrix(ListVect);
#  NSP:=NullspaceIntMat(RemoveFractionMatrix(ListVect));
  NSP:=NullspaceMat(ListVect);
  nbVect:=Length(ListVect);
  TheDim:=Length(ListVect[1]);
  nbRelation:=Length(NSP);
  ListInequalities:=[];
  SetVectorPos:=[];
  for iVect in TheConstraint.ListStrictlyPositive
  do
    H:=[-1];
    for iRel in [1..nbRelation]
    do
      Add(H, NSP[iRel][iVect]);
    od;
    Add(ListInequalities, H);
    AddSet(SetVectorPos, iVect);
  od;
  for iVect in TheConstraint.ListPositive
  do
    H:=[0];
    for iRel in [1..nbRelation]
    do
      Add(H, NSP[iRel][iVect]);
    od;
    Add(ListInequalities, H);
    AddSet(SetVectorPos, iVect);
  od;
  for eSet in TheConstraint.ListSetStrictPositive
  do
    H:=[-1];
    for iRel in [1..nbRelation]
    do
      TheSum:=0;
      for iVect in eSet
      do
        TheSum:=TheSum+NSP[iRel][iVect];
        AddSet(SetVectorPos, iVect);
      od;
      Add(H, TheSum);
    od;    
    Add(ListInequalities, H);
  od;
  ToBeMinimized:=[0];
  for iRel in [1..nbRelation]
  do
    TheSum:=0;
    for iVect in SetVectorPos
    do
      TheSum:=TheSum+NSP[iRel][iVect];
    od;
    Add(ToBeMinimized, TheSum);
  od;
#  Print("|ListInequalities|=", Length(ListInequalities), " |ListInequalities[1]|=", Length(ListInequalities[1]), "\n");
#  SaveDataToFile("DebugLPprogram", rec(ListInequalities:=ListInequalities, ToBeMinimized:=ToBeMinimized));
  TheLP:=LinearProgramming(ListInequalities, ToBeMinimized);
#  SaveDataToFile("DebugLPprogramSolution", rec(ListInequalities:=ListInequalities, ToBeMinimized:=ToBeMinimized, TheLP:=TheLP));
#  Print("ListInequalities=");
#  PrintArray(ListInequalities);
#  Print("ToBeMinimized=", ToBeMinimized, "\n");
#  Print("TheLP=", TheLP, "\n");
  if IsBound(TheLP.primal_solution) then
    TheSolutionRed:=ListWithIdenticalEntries(nbVect, 0);
    for eEnt in TheLP.primal_solution
    do
      TheSolutionRed[eEnt[1]]:=eEnt[2];
    od;
    TheSolution:=TheSolutionRed*NSP;
    for iVect in TheConstraint.ListStrictlyPositive
    do
      if ArithFct.IsNegative(TheSolution[iVect]) then
        Error("Inconsistency SearchPositiveRelation, case 1");
      fi;
    od;
    for iVect in TheConstraint.ListPositive
    do
      if ArithFct.IsStrictlyNegative(TheSolution[iVect]) then
        Error("Inconsistency SearchPositiveRelation, case 2");
      fi;
    od;
    for eSet in TheConstraint.ListSetStrictPositive
    do
      TheSum:=0;
      for iVect in eSet
      do
        TheSum:=TheSum+TheSolution[iVect];
      od;
      if ArithFct.IsNegative(TheSum) then
        Error("Inconsistency SearchPositiveRelation, case 3");
      fi;
    od;
    TheProd:=TheSolution*ListVect;
    if TheProd<>ListWithIdenticalEntries(TheDim, 0) then
      Error("Inconsistency SearchPositiveRelation, case 3");
    fi;
    return TheSolution;
  else
    return false;
    # We need to program a correct dual way to get a certificate
    # there is thinking to be made.
#    TheCertif:=SearchNonExistencePositiveRelation(ListVect, ListStatus);
#    if TheCertif=false then
#      Print("We failed to get the certificate of non-existence\n");
#      Print("Should we panic? probably yes");
#    fi;
  fi;
end;



SearchPositiveRelationSimple:=function(ListVect)
  local TheConstraint;
  TheConstraint:=rec(ListStrictlyPositive:=[  ],
                     ListPositive:=[1..Length(ListVect)],
                     ListSetStrictPositive:=[[1..Length(ListVect)]]);
  return SearchPositiveRelation(ListVect, TheConstraint);
end;



SearchCertificateNoPositiveRelationSimple:=function(ListIneq)
  local nbIneq, TheDim, ListTotIneq, ToBeMinimized, eIneq, fIneq, TheLP, TheReturn;
  nbIneq:=Length(ListIneq);
  TheDim:=Length(ListIneq[1]);
  ListTotIneq:=[];
  ToBeMinimized:=ListWithIdenticalEntries(TheDim,0);
  for eIneq in ListIneq
  do
    fIneq:=Concatenation([-1], RemoveFraction(eIneq));
    Add(ListTotIneq, fIneq);
    ToBeMinimized:=ToBeMinimized + fIneq;
  od;
  TheLP:=LinearProgramming(ListTotIneq, ToBeMinimized);
  TheReturn:=rec(TheLP:=TheLP);
  return TheReturn;
end;



SolutionMatNonnegative:=function(ListVect, eVect)
  local InputListVect, nb, TheConstraint, eReply, TheResult;
  InputListVect:=Concatenation(ListVect, [-eVect]);
  nb:=Length(ListVect);
  TheConstraint:=rec(ListStrictlyPositive:=[  ],
                     ListPositive:=[1..nb+1],
                     ListSetStrictPositive:=[[1..nb], [nb+1]]);
  TheResult:=SearchPositiveRelation(InputListVect, TheConstraint);
  if TheResult=false then
    return fail;
  fi;
  eReply:=TheResult{[1..nb]}/TheResult[nb+1];
  if Minimum(eReply) < 0 then
    Error("Found coefficients that are negative");
  fi;
  if eReply*ListVect<>eVect then
    Error("There are bugs to be solved");
  fi;
  return eReply;
end;



SolutionMatStrictlyPositive:=function(ListVect, eVect)
  local InputListVect, nb, TheConstraint, eReply, TheResult, eListB, iE;
  InputListVect:=Concatenation(ListVect, [-eVect]);
  nb:=Length(ListVect);
  eListB:=[];
  for iE in [1..nb+1]
  do
    Add(eListB, [iE]);
  od;
  TheConstraint:=rec(ListStrictlyPositive:=[  ],
                     ListPositive:=[1..nb+1],
                     ListSetStrictPositive:=eListB);
  TheResult:=SearchPositiveRelation(InputListVect, TheConstraint);
  if TheResult=false then
    return fail;
  fi;
  eReply:=TheResult{[1..nb]}/TheResult[nb+1];
  if Minimum(eReply) <= 0 then
    Error("Found coefficients that are not strictly positive");
  fi;
  if eReply*ListVect<>eVect then
    Error("There are bugs to be solved");
  fi;
  return eReply;
end;


# This will guarantee that the first coordinate of all vectors of EXT
# is non-negative.
FacetizationCone:=function(EXT, BoundingFac)
  local TheSum, EXTtot, EXTbas, eInvMat, EXT_ret, BoundingFac_ret;
  TheSum:=Sum(EXT);
  EXTtot:=Concatenation([TheSum], EXT);
  EXTbas:=RowReduction(EXTtot).EXT;
  Print("EXTbas=\n");
  PrintArray(EXTbas);
  eInvMat:=Inverse(EXTbas);
  EXT_ret:=EXT*eInvMat;
  #
  if Length(BoundingFac) > 0 then
    BoundingFac_ret:=BoundingFac*TransposedMat(EXTbas);
  else
    BoundingFac_ret:=[];
  fi;
  return rec(EXT:=EXT_ret, BoundingFac:=BoundingFac_ret);
end;


# We need to have EXT of full rank
#
# BoundingFac is a set of relevant inequality on EXT
# which can be empty.
# It does not have to be invariant under the group.
#
# So for each inequality we do following:
# ---Determine the list of known facets  F that are incident to e.
# ---If f is not relevant then it can be written as
#     e = sum_i alpha_i e_i     with     alpha_i >= 0
#     For any facet f in F, we have f.e = 0
#     Thus the inequality relevant must have f.e_i = 0.
# ---For an orbit, if any one is matched as being removable, then
#    the whole orbit is removable.
#
# The size of the BoundingFac has to be chosen carefully. In most cases it is empty.
KernelEliminationByRedundancyEquivariant:=function(EXT, BoundingFac, GRPperm, FCTstab)
  local eRec_proc, EXT_work, BoundingFac_work, nbVert, TheDim, ListStatus, FuncTest, FuncTest_Any, TestDegeneracy, iExt, eOrb, ListDone, ListPermGens, eList, PermGRPred, eSetSelect, eGen;
  eRec_proc:=FacetizationCone(EXT, BoundingFac);
  EXT_work:=eRec_proc.EXT;
  BoundingFac_work:=eRec_proc.BoundingFac;
  nbVert:=Length(EXT_work);
  TheDim:=Length(EXT_work[1]);
  ListStatus:=ListWithIdenticalEntries(Length(EXT_work), 1);
  ListDone:=ListWithIdenticalEntries(Length(EXT_work), 0);
  FuncTest:=function(eExt, VFAC)
    local eFac;
    for eFac in VFAC
    do
      if eExt*eFac<>0 then
        return false;
      fi;
    od;
    return true;
  end;
  FuncTest_Any:=function(ListExt, VFAC)
    local eEXT;
    for eEXT in ListExt
    do
      if FuncTest(eEXT, VFAC)=false then
        return false;
      fi;
    od;
    return true;
  end;
  TestDegeneracy:=function(iEXT)
    local eEXTtest, ListB, eFac, TheStab, LSet, O, ListVect, ListStrictlyPositive, ListPositive, ListSetStrictPositive, idx, eO, eSum, eV, TheConstraint, eSolution, TheLP, TheDiff;
    # Returns true if the ray is indeed degenerate (and so should be removed)
    # Returns false if the vector is indeed extreme.
    eEXTtest:=EXT_work[iEXT];
    ListB:=Filtered(BoundingFac_work, eFac->eFac*eEXTtest=0);
    TheStab:=FCTstab(iEXT);
    TheDiff:=Filtered([1..nbVert], x->ListStatus[x]=1 and x<>iEXT);
    O:=Orbits(TheStab, TheDiff, OnPoints);
    ListVect:=[];
    for eO in O
    do
      if FuncTest_Any(EXT_work{eO}, ListB) then
        eSum:=ListWithIdenticalEntries(TheDim,0);
        for eV in eO
        do
          eSum:=eSum+EXT_work[eV];
        od;
        Add(ListVect, eSum/Length(eO));
      fi;
    od;
    if Length(ListVect)=0 then
      return false;
    fi;
    TheLP:=LinearProgramming(ListVect, eEXTtest);
    if IsBound(TheLP.optimal)=false then
      return false;
    fi;
    if TheLP.optimal<0 then
      return false;
    fi;
    return true;
  end;
  for iExt in [1..nbVert]
  do
    if ListDone[iExt]=0 then
      eOrb:=Orbit(GRPperm, iExt, OnPoints);
      if TestDegeneracy(iExt) then
        ListStatus{eOrb}:=ListWithIdenticalEntries(Length(eOrb), 0);
      fi;
      ListDone{eOrb}:=ListWithIdenticalEntries(Length(eOrb), 1);
    fi;
  od;
  eSetSelect:=Filtered([1..nbVert], x->ListStatus[x]=1);
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(GRPperm)
  do
    eList:=OnTuples(eSetSelect, eGen);
    Add(ListPermGens, SortingPerm(eList));
  od;
  PermGRPred:=Group(ListPermGens);
  return rec(eSetSelect:=eSetSelect, PermGRPred:=PermGRPred);
end;



EliminationByRedundancyEquivariant:=function(EXT, BoundingSet, GRPperm)
  local FCTstab;
  FCTstab:=function(i)
    return Stabilizer(GRPperm, i, OnPoints);
  end;
  return KernelEliminationByRedundancyEquivariant(EXT, BoundingSet, GRPperm, FCTstab);
end;



RemoveRedundancy:=function(EXT)
  local GRPperm, BoundingSet, eRec, EXTset;
  EXTset:=Set(List(EXT, RemoveFraction));
  GRPperm:=LinPolytope_Automorphism(EXTset);
  BoundingSet:=[];
  eRec:=EliminationByRedundancyEquivariant(EXTset, BoundingSet, GRPperm);
  return EXTset{eRec.eSetSelect};
end;


IsSolutionToLinearProgNonDegenerate:=function(ListInequalities, ToBeMinimized, TheVertex)
  local n, ListMatchingIneq, eIneq, eIneqRed, nbIneq, TheConstraint, eSolPositive;
  n:=Length(ToBeMinimized)-1;
  ListMatchingIneq:=[];
  for eIneq in ListInequalities
  do
    if eIneq*TheVertex=0 then
      eIneqRed:=eIneq{[2..n+1]};
      Add(ListMatchingIneq, eIneqRed);
    fi;
  od;
  eIneqRed:=ToBeMinimized{[2..n+1]};
  Add(ListMatchingIneq, -eIneqRed);
  nbIneq:=Length(ListMatchingIneq);
  TheConstraint:=rec(ListStrictlyPositive:=[1..nbIneq], ListPositive:=[], ListSetStrictPositive:=[]);
  eSolPositive:=SearchPositiveRelation(ListMatchingIneq, TheConstraint);
  if eSolPositive=false then
    return false;
  else
    return true;
  fi;
end;





#
#
# We use the linear programming method for testing adjacency
# The set BSet is a list of facet that help removing irrelevant extreme rays
TestAdjacency:=function(V1, V2, EXT, BoundingSet)
  local SYSRED, iVect, iCol, VS, eBS, eExt, SBoundingSet, test, Mat1, Mat2, Mat12, r1, r2, r12, RED, VSE, TheLP;
  SBoundingSet:=Filtered(BoundingSet, x->x*V1=0 and x*V2=0);
  SYSRED:=[];
  for eExt in EXT
  do
    if eExt<>V1 and eExt<>V2 then
      test:=1;
      for eBS in SBoundingSet
      do
        if eExt*eBS>0 then
          test:=0;
        fi;
      od;
      if test=1 then
        Add(SYSRED, eExt);
      fi;
    fi;
  od;
  if Length(SYSRED)<=1 then
    return true;
  fi;
  Mat1:=[V1];
  Mat2:=[V2];
  Mat12:=[V1, V2];
  for eExt in SYSRED
  do
    Add(Mat1, eExt);
    Add(Mat2, eExt);
    Add(Mat12, eExt);
  od;
  r1:=RankMat(Mat1);
  r2:=RankMat(Mat2);
  r12:=RankMat(Mat12);
  if r12 > r1 or r12 > r2 then
    return true;
  fi;
  RED:=ColumnReduction(Mat12, r12).EXT;
  VSE:=RED{[3..Length(RED)]};
  Add(VSE, -RED[2]);
  TheLP:=LinearProgramming(VSE, RED[1]);
  if IsBound(TheLP.optimal)=false then
    return true;
  fi;
  if TheLP.optimal<0 then
    return true;
  fi;
  return false;
#  if A="non zero optimum\n" then
#    return true;
#  else
#    return false;
#  fi;
end;




FuncRepresentationMatrix:=function(TheGraph, GroupExt)
  local nbElt, ListORB, iOrb, TheROW, eVert, Stab, jOrb, nbij, O2, eO2, fVert, Matr;
  Matr:=[];
  nbElt:=TheGraph.order;
  ListORB:=Orbits(GroupExt, [1..nbElt], OnPoints);
  for iOrb in [1..Length(ListORB)]
  do
    TheROW:=[];
    eVert:=ListORB[iOrb][1];
    Stab:=Stabilizer(GroupExt, eVert, OnPoints);
    for jOrb in [1..Length(ListORB)]
    do
      nbij:=0;
      O2:=Orbits(Stab, ListORB[jOrb], OnPoints);
      for eO2 in O2
      do
        fVert:=eO2[1];
        if IsEdge(TheGraph, [eVert,fVert])=true then
          nbij:=nbij+Length(eO2);
        fi;
      od;
      TheROW[jOrb]:=nbij;
    od;
    Add(Matr, TheROW);
  od;
  return Matr;
end;


__RepresentativeOrbitTwoSet:=function(GroupExt, ConsideredSet)
  local ListORB, OrbitEdgeSet, Stab, eVert, iOrb, jOrb, PartialListCand, FuncInsert, U, eO2, nbORB, fVert;
#  Print("Beginning of __RepresentativeOrbitTwoSet\n");
  ListORB:=Orbits(GroupExt, ConsideredSet, OnPoints);
  nbORB:=Length(ListORB);
  OrbitEdgeSet:=[];
  for iOrb in [1..nbORB]
  do
#    Print("iOrb=", iOrb, " / ", nbORB, "\n");
    eVert:=ListORB[iOrb][1];
    Stab:=Stabilizer(GroupExt, eVert, OnPoints);
    for jOrb in [iOrb..nbORB]
    do
      PartialListCand:=[];
      if iOrb=jOrb then
        FuncInsert:=function(eSet)
          local fSet;
          for fSet in PartialListCand
          do
            if RepresentativeAction(GroupExt, fSet, eSet, OnSets)<>fail then
              return;
            fi;
          od;
          Add(PartialListCand, eSet);
        end;
        U:=Difference(ListORB[jOrb], [eVert]);
      else
        FuncInsert:=function(eSet)
          Add(PartialListCand, eSet);
        end;
        U:=ListORB[jOrb];
      fi;
      for eO2 in Orbits(Stab, U, OnPoints)
      do
        fVert:=eO2[1];
        FuncInsert(Set([eVert, fVert]));
      od;
      Append(OrbitEdgeSet, PartialListCand);
    od;
  od;
  return OrbitEdgeSet;
end;



EquivariantSkeleton:=function(GroupExt, nbElt, FuncAdjacent)
  local eEdge, Skeleton, ListOrb, iEdge, nbOrb;
  Skeleton:=NullGraph(GroupExt, nbElt);
  # running adjacency search...
  ListOrb:=__RepresentativeOrbitTwoSet(GroupExt, [1..nbElt]);
  nbOrb:=Length(ListOrb);
  Print("|ListOrb|=", nbOrb, "\n");
  for iEdge in [1..nbOrb]
  do
    Print("iEdge=", iEdge, "/", nbOrb, "\n");
    eEdge:=ListOrb[iEdge];
    if FuncAdjacent(eEdge[1], eEdge[2]) then
      AddEdgeOrbit(Skeleton, [eEdge[1], eEdge[2]]);
      AddEdgeOrbit(Skeleton, [eEdge[2], eEdge[1]]);
    fi;
  od;
  return Skeleton;
end;




SkeletonGraph:=function(GroupExt, EXT, BoundingSet)
  local FAC, RecRed, rnk, Hmat, i, i2, j, FuncAdj, HmatInv, BoundFAC, eBoundExt, ListScal, eFac;
  FAC:=FacetizationCone(EXT);
  RecRed:=RowReduction(EXT);
  rnk:=Length(RecRed.Select);
  Hmat:=NullMat(rnk, rnk);
  for i in [1..rnk]
  do
    i2:=RecRed.Select[i];
    for j in [1..rnk]
    do
      Hmat[i][j]:=FAC[i2][j];
    od;
  od;
  HmatInv:=Inverse(Hmat);
  BoundFAC:=[];
  for eBoundExt in BoundingSet
  do
    ListScal:=List(RecRed.EXT, x->x*eBoundExt);
    eFac:=ListScal*HmatInv;
    if Minimum(FAC*eFac)<0 then
      Error("Inconsistency in BoundFAC");
    fi;
    Add(BoundFAC, eFac);
  od;
  FuncAdj:=function(S1,S2)
    return TestAdjacency(FAC[S1], FAC[S2], FAC, BoundFAC);
  end;
  return EquivariantSkeleton(GroupExt, Length(FAC), FuncAdj);
end;


LP_GetSet:=function(FAC, eMinimize)
  local TheLP, eVect, eEnt, eVectExt, eSet, nbVert, TheDim;
  TheLP:=LinearProgramming(FAC, eMinimize);
  nbVert:=Length(FAC);
  TheDim:=Length(FAC[1]);
  if IsBound(TheLP.primal_solution) then
    eVect:=ListWithIdenticalEntries(TheDim,0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    eVectExt:=Concatenation([1], eVect);
    eSet:=Filtered([1..nbVert], x->FAC[x]*eVectExt=0);
    if RankMat(FAC{eSet})=TheDim-1 then
      return eSet;
    fi;
    return fail;
  fi;
  return fail;
end;


LP_GetExpressionForLP:=function(EXT)
  local OneVert, ListDiff, eEXT, TheBasis, TheDim, NewListCoord, eVectSol, eIso, eVect;
  OneVert:=EXT[1];
  ListDiff:=[];
  for eEXT in EXT
  do
    Add(ListDiff, eEXT-OneVert);
  od;
  TheBasis:=RowReduction(ListDiff).EXT;
  TheDim:=Length(TheBasis);
  NewListCoord:=[];
  for eVect in ListDiff
  do
    eVectSol:=Concatenation([1], SolutionMat(TheBasis, eVect));
    Add(NewListCoord, eVectSol);
  od;
  eIso:=Isobarycenter(NewListCoord);
  eIso[1]:=0;
  return List(NewListCoord, x->x-eIso);
end;

GetInitialRaysEXT:=function(EXT, nb)
  local nbVert, EXT_lp, GetSet, ListSet, i, TheDim;
  nbVert:=Length(EXT);
  if Set(List(EXT, x->x[1]))<>[1] then
    Error("The first coordinate needs to be 1 for all vectors");
  fi;
  EXT_lp:=LP_GetExpressionForLP(EXT);
  TheDim:=Length(EXT_lp[1])-1;
  GetSet:=function()
    local siz, eMinimize, i, test;
    siz:=3;
    while(true)
    do
      eMinimize:=[1];
      for i in [1..TheDim]
      do
        Add(eMinimize, Random([-siz..siz]));
      od;
      test:=LP_GetSet(EXT_lp, eMinimize);
      if test<>fail then
        return test;
      fi;
      siz:=siz+1;
    od;
  end;
  ListSet:=[];
  for i in [1..nb]
  do
    Print("GetInitialRaysEXT i=", i, " / ", nb, "\n");
    Add(ListSet, GetSet());
  od;
  return ListSet;
end;


# We know that eVect is not in the cone spanned by EXT.
# We want a facet violated F of EXT with F.eVect < 0
GetViolatedFacet:=function(EXT, eVect)
  local TheDim, len, EXTcall, EXTpoly, EXT_lp, TheCritFacet, nbIter, eMinimize, test, eFAC, GetOneFacetDefiningVect, i, eSelect, eVectRed, EXTred;
  if Length(EXT[1])<>Length(eVect) then
    Error("EXT and eVect should be of the same dimension");
  fi;
  eSelect:=ColumnReduction(EXT).Select;
  len:=Length(EXT);
  EXTcall:=Concatenation(EXT, [-eVect]);
  EXTpoly:=PolytopizationGeneralCone(EXTcall);
#  Print("EXTpoly (", Length(EXTpoly), " / ", Length(EXTpoly[1]), ") \n");
#  PrintArray(EXTpoly);
#  Print("RankMat(EXTpoly)=", RankMat(EXTpoly), "\n");
  #
  EXT_lp:=LP_GetExpressionForLP(EXTpoly);
#  Print("EXT_lp=\n");
#  PrintArray(EXT_lp);
#  Print("RankMat(EXT_lp)=", RankMat(EXT_lp), "\n");
  TheDim:=Length(EXT_lp[1])-1;
  TheCritFacet:=EXT_lp[len+1];
  GetOneFacetDefiningVect:=function()
    local siz, eMinimize, i, test;
    siz:=3;
    while(true)
    do
      eMinimize:=[1];
      for i in [1..TheDim]
      do
        Add(eMinimize, Random([-siz..siz]));
      od;
      test:=LP_GetSet(EXT_lp, eMinimize);
      if test<>fail then
        return eMinimize;
      fi;
      siz:=siz+1;
    od;
  end;
  nbIter:=20;
  while(true)
  do
    #
    eMinimize:=GetOneFacetDefiningVect();
    for i in [1..nbIter]
    do
      test:=LP_GetSet(EXT_lp, eMinimize);
      if test<>fail then
        if Position(test, len+1)=fail then
          EXTred:=List(EXT, x->x{eSelect});
          eFAC:=__FindFacetInequality(EXTred, test);
          if Minimum(List(EXTred, x->x*eFAC))<0 then
            Error("We did not find a facet");
          fi;
          eVectRed:=eVect{eSelect};
          if eVectRed*eFAC >= 0 then
            Error("The facet does not separate as expected");
          fi;
          return test;
        fi;
      fi;
      eMinimize:=eMinimize - TheCritFacet;
    od;
    nbIter:=nbIter+1;
  od;
end;



GetInitialRaysGeneral:=function(FAC, nb)
  local NewListIneq;
  NewListIneq:=PolytopizationGeneralCone(FAC);
  return GetInitialRaysEXT(NewListIneq, nb);
end;


GetInitialRays_LinProg:=function(EXT, nb)
  local IsEXT, eEXT;
  Print("Beginning of GetInitialRays_LinProg\n");
  IsEXT:=true;
  for eEXT in EXT
  do
    if eEXT[1]<>1 then
      IsEXT:=false;
    fi;
  od;
  Print("IsEXT=", IsEXT, "\n");
  if IsEXT=true then
    return GetInitialRaysEXT(EXT, nb);
  fi;
  return GetInitialRaysGeneral(EXT, nb);
end;

GetInitialRays_LinProg_sampling:=function(PermGRP, EXT, nbIter)
  local ListOrbitLinProg, FuncInsert, iter, ListSet, eSet;
  ListOrbitLinProg:=[];
  FuncInsert:=function(eSet)
    local eOrbit;
    for eOrbit in ListOrbitLinProg
    do
      if RepresentativeAction(PermGRP, eSet, eOrbit, OnSets)<>fail then
        return;
      fi;
    od;
    Print("Find a new orbit of length ", Length(eSet), "\n");
    Add(ListOrbitLinProg, eSet);
  end;
  for iter in [1..nbIter]
  do
    Print("iter=", iter, "/", nbIter, "\n");
    ListSet:=GetInitialRays_LinProg(EXT, 10);
    for eSet in ListSet
    do
      FuncInsert(eSet);
    od;
  od;
  return ListOrbitLinProg;
end;

KernelLinearDeterminedByInequalities:=function(FAC)
  local n, nbFac, eReply, ListIdx, NSP, FACproj, FACprojCor, TheSpann, TheSpannHigh;
  n:=Length(FAC[1]);
  nbFac:=Length(FAC);
#  Print("Before call to SearchPositiveRelationSimple\n");
  eReply:=SearchPositiveRelationSimple(FAC);
#  Print("After call to SearchPositiveRelationSimple\n");
  if eReply=false then
    return IdentityMat(n);
  else
    ListIdx:=Filtered([1..nbFac], x->eReply[x]>0);
    NSP:=NullspaceMat(TransposedMat(FAC{ListIdx}));
    if Length(NSP)=0 then
      return [];
    fi;
    FACproj:=FAC*TransposedMat(NSP);
    FACprojCor:=Filtered(FACproj, x->x*x>0);
    if Length(FACprojCor)=0 then
      TheSpann:=IdentityMat(Length(NSP));
    else
      TheSpann:=KernelLinearDeterminedByInequalities(FACprojCor);
    fi;
    if Length(TheSpann)=0 then
      TheSpannHigh:=[];
    else
      TheSpannHigh:=TheSpann*NSP;
    fi;
    return TheSpannHigh;
  fi;
end;

LinearDeterminedByInequalities:=function(FAC)
  local FACsel;
  FACsel:=Filtered(FAC, x->x*x>0);
  return KernelLinearDeterminedByInequalities(FACsel);
end;


#
# A cone is given by a family of extreme rays.
# An interior point is given and the goal is to find a face that
# contains this point.
GetContainingFacet:=function(EXT, ePoint)
  local n, nbEXT, eSol, eIncdPart, iEXT, NSP, IsInFace, eIncdTot, TheSpace, TheSpaceFunc, ListIneq, eIneq, eBas;
  n:=Length(EXT[1]);
  nbEXT:=Length(EXT);
  if ePoint=ListWithIdenticalEntries(n,0) then
    return [1..nbEXT];
  fi;
  eSol:=SolutionMatNonnegative(EXT, ePoint);
  if eSol=fail then
    Print("The point ePoint=", ePoint, " is not contained in EXT\n");
    Error("Please solve your error");
  fi;
  eIncdPart:=[];
  for iEXT in [1..nbEXT]
  do
    if eSol[iEXT]>0 then
      Add(eIncdPart, iEXT);
    fi;
  od;
  # eIncdPart does not necessarily defines a facet
  # We define the set of all functions that cancels on the
  # NSP and are nonnegative
  NSP:=NullspaceMat(TransposedMat(EXT{eIncdPart}));
  if Length(NSP)=0 then
    return [1..Length(EXT)];
  fi;
  ListIneq:=[];
  for iEXT in Difference([1..nbEXT], eIncdPart)
  do
    eIneq:=List(NSP, x->x*EXT[iEXT]);
    Add(ListIneq, eIneq);
  od;
  # Now we look at the space defined by this
  TheSpace:=LinearDeterminedByInequalities(ListIneq);
  TheSpaceFunc:=[];
  for eBas in TheSpace
  do
    Add(TheSpaceFunc, eBas*NSP);
  od;
  IsInFace:=function(eEXT)
    local eVect;
    for eVect in TheSpaceFunc
    do
      if eVect*eEXT<>0 then
        return false;
      fi;
    od;
    return true;
  end;
  eIncdTot:=[];
  for iEXT in [1..nbEXT]
  do
    if IsInFace(EXT[iEXT]) then
      Add(eIncdTot, iEXT);
    fi;
  od;
  return eIncdTot;
end;




IsSpaceFullDimensional:=function(FAC)
  local FACsel, eReply;
  FACsel:=Filtered(FAC, x->x*x>0);
  eReply:=SearchPositiveRelationSimple(FAC);
  if eReply=false then
    return true;
  else
    return false;
  fi;
end;






AreInequalitiesDefiningPolytope:=function(FAC)
  local n, eVect, nbIneq, ListVect, TheConstraint, eReply, ListEqua, ListRemaining, iIneq, NSP, ListIneqRed, ListScal, SpaceRed;
  n:=Length(FAC[1]);
  eVect:=ListWithIdenticalEntries(n,0);
  eVect[1]:=1;
  nbIneq:=Length(FAC);
  ListVect:=Concatenation([eVect], -FAC);
  TheConstraint:=rec(ListStrictlyPositive:=[1], ListPositive:=[2..nbIneq+1], ListSetStrictPositive:=[]);
  eReply:=SearchPositiveRelation(ListVect, TheConstraint);
  if eReply=false then
    return false;
  fi;
  ListEqua:=[];
  ListRemaining:=[];
  for iIneq in [1..nbIneq]
  do
    if eReply[iIneq+1]>0 then
      Add(ListEqua, FAC[iIneq]);
    else
      Add(ListRemaining, iIneq);
    fi;
  od;
  NSP:=NullspaceMat(TransposedMat(ListEqua));
  if Length(NSP)=0 then
    return true;
  fi;
  ListIneqRed:=[];
  for iIneq in ListRemaining
  do
    ListScal:=List(NSP, x->x*FAC[iIneq]);
    Add(ListIneqRed, ListScal);
  od;
  SpaceRed:=LinearDeterminedByInequalities(ListIneqRed);
  if Length(SpaceRed)=0 then
    return true;
  else
    return false;
  fi;
end;





ReductionLinearProgram:=function(ListIneq, ToBeMinimized)
  local SetIneq, eRecSol, TheDim, fVect, eFace, eVect, eEnt, eVectExt, FirstCol, eBasisA, eBasisB, NewVect, i, nbIneqSet, SetZero, SetNonZero, ExtBasis, FACatt, iIneq, jIneq, eIneq, LScal, FACset, FACsetRed, TotalSet, eFac, eSetA, eSetB, SetSetIneq, SetListIneq, iFAC, eSetC;
  SetIneq:=Set(ListIneq);
  eRecSol:=LinearProgramming(SetIneq, ToBeMinimized);
  if IsBound(eRecSol.optimal)=false then
    return [1..Length(ListIneq)];
  fi;
  TheDim:=Length(ListIneq[1])-1;
  fVect:=Concatenation([ToBeMinimized[1] - eRecSol.optimal], ToBeMinimized{[2..TheDim+1]});
  eFace:=LinearDeterminedByInequalities(Concatenation(SetIneq, [-fVect]));
  eVect:=ListWithIdenticalEntries(TheDim,0);
  for eEnt in eRecSol.primal_solution
  do
    eVect[eEnt[1]]:=eEnt[2];
  od;
  eVectExt:=Concatenation([1], eVect);
  #
  FirstCol:=List(eFace, x->x[1]);
  eBasisA:=NullspaceMat(TransposedMat([FirstCol]));
  eBasisB:=[];
  for eVect in eBasisA
  do
    NewVect:=ListWithIdenticalEntries(TheDim+1,0);
    for i in [1..Length(eFace)]
    do
      NewVect:=NewVect + eVect[i]*eFace[i];
    od;
    Add(eBasisB, NewVect);
  od;
  #
  nbIneqSet:=Length(SetIneq);
  SetZero:=Filtered([1..nbIneqSet], x->First(eFace, y->y*SetIneq[x]<>0)=fail);
  SetNonZero:=Difference([1..nbIneqSet], SetZero);
  ExtBasis:=Concatenation([eVectExt], eBasisB);
  FACatt:=[];
  for iIneq in SetNonZero
  do
    eIneq:=SetIneq[iIneq];
    LScal:=List(ExtBasis, x->eIneq*x);
    Add(FACatt, RemoveFraction(LScal));
  od;
  FACset:=Set(FACatt);
  #
  FACsetRed:=RemoveRedundancy(FACset);
  TotalSet:=[];
  for eFac in FACsetRed
  do
    eSetA:=Filtered([1..Length(SetNonZero)], x->FACatt[x]=eFac);
    eSetB:=SetNonZero{eSetA};
    Append(TotalSet, eSetB);
  od;
  SetSetIneq:=Union(Set(TotalSet), Set(SetZero));
  SetListIneq:=[];
  for iFAC in SetSetIneq
  do
     eSetC:=Filtered([1..Length(ListIneq)], x->ListIneq[x]=SetIneq[iFAC]);
     Append(SetListIneq, eSetC);
  od;
  return Set(SetListIneq);
end;




# We assume that the integer linear program considered
# has a solution (no primal_direction, optimal well defined
# when solving over the rationals).
#
# The system is expressed as
# A x^T >= a
# B x^T  = b
# optimize x c
GLPK_LinearProgrammingPlusEqua_General_SparseMat:=function(Aspmat, ListAconst, Bspmat, ListBconst, ToBeMinimized, StrType, RecOpt)
  local FileOut, FileOutRes, FileMath, nbVar, nbIneq, output, iVar, PrintConstraintVector, eVect, iIneq, eIneq, TheCommand1, TheCommand2, TheResult, FileErr1, FileErr2, eSolExt, iConst, nbEqua, iEqua, eEqua, eEnt;
  if IsIntegralVector(ToBeMinimized)=false then
    Error("For integral programming, the constraint must be integral");
  fi;
  FileOut:=Filename(POLYHEDRAL_tmpdir, "GLP.out");
  FileErr1:=Filename(POLYHEDRAL_tmpdir, "GLP.err1");
  FileErr2:=Filename(POLYHEDRAL_tmpdir, "GLP.err2");
  FileOutRes:=Filename(POLYHEDRAL_tmpdir, "GLP.outres");
  FileMath:=Filename(POLYHEDRAL_tmpdir, "GLP.mod");
  nbVar:=Aspmat.nbCol;
  nbIneq:=Aspmat.nbLine;
  output:=OutputTextFile(FileMath, true);
  AppendTo(output, "# GLPK_LinearProgrammingPlusEqua_General_SparseMat\n");
  for iVar in [1..nbVar]
  do
    if StrType="rational" then
      AppendTo(output, "var x", iVar, ";\n");
    else
      AppendTo(output, "var x", iVar, ", ", StrType, ";\n");
    fi;
  od;
  #
  PrintConstraintVector:=function(eEnt)
    local len, iVar, eVal, IsFirst, i;
    IsFirst:=true;
    len:=Length(eEnt.ListVal);
    for i in [1..len]
    do
      iVar:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      if eVal<>0 then
        if IsFirst then
          if eVal=1 then
            AppendTo(output, " x", iVar);
          elif eVal=-1 then
            AppendTo(output, " - x", iVar);
          elif eVal < 0 then
            AppendTo(output, " - ", -eVal, " * x", iVar);
          else
            AppendTo(output, " ", eVal, " * x", iVar);
          fi;
        else
          if eVal=1 then
            AppendTo(output, " + x", iVar);
          elif eVal=-1 then
            AppendTo(output, " - x", iVar);
          elif eVal < 0 then
            AppendTo(output, " - ", -eVal, " * x", iVar);
          else
            AppendTo(output, " + ", eVal, " * x", iVar);
          fi;
        fi;
        IsFirst:=false;
      fi;
    od;
  end;
  AppendTo(output, "minimize obj:");
  eVect:=ToBeMinimized{[2..nbVar+1]};
  if First(ToBeMinimized, x->x<>0)=fail then
    Print("ToBeMinimized=", ToBeMinimized, "\n");
    Print("ToBeMinimized needs to be nontrivial\n");
    Error("Please debug that problem in your code");
  fi;
  eEnt:=rec(ListCol:=[1..nbVar], ListVal:=eVect);
  PrintConstraintVector(eEnt);
  AppendTo(output, ";\n");
  #
  iConst:=0;
  for iIneq in [1..nbIneq]
  do
    iConst:=iConst+1;
    AppendTo(output, "s.t. c", iConst, ":");
    eEnt:=Aspmat.ListEntries[iIneq];
    PrintConstraintVector(eEnt);
    AppendTo(output, " >= ", ListAconst[iIneq], ";\n");
  od;
  nbEqua:=Bspmat.nbLine;
  for iEqua in [1..nbEqua]
  do
    eEnt:=Bspmat.ListEntries[iEqua];
    if eEnt.ListVal<>ListWithIdenticalEntries(Length(eEnt.ListVal), 0) then
      iConst:=iConst+1;
      AppendTo(output, "s.t. c", iConst, ":");
      PrintConstraintVector(eEnt);
      AppendTo(output, " = ", ListBconst[iEqua], ";\n");
    else
      if ListBconst[iEqua]<>0 then
        return rec(Status:="Undefined");
      fi;
    fi;
  od;
  #
  AppendTo(output, "solve;\n");
  AppendTo(output, "display");
  for iVar in [1..nbVar]
  do
    if iVar>1 then
      AppendTo(output, ",");
    fi;
    AppendTo(output, " x", iVar);
  od;
  AppendTo(output, ";\n");
  AppendTo(output, "end;\n");
  CloseStream(output);
  #
  TheCommand1:=Concatenation(FileGlpsol, RecOpt.optimString, " --output ", FileOut, " --math ", FileMath, " > ", FileErr1, " 2> ", FileErr2);
  Print("TheCommand1=", TheCommand1, "\n");
  Exec(TheCommand1);
#  Print(NullMat(5));
  #
  TheCommand2:=Concatenation(FileGLPSOL_ExtractXsol, " ", FileOut, " > ", FileOutRes);
#  Print("TheCommand2=", TheCommand2, "\n");
#  if StrType="integer" then
#    Print(NullMat(5));
#  fi;
  Exec(TheCommand2);
  #
  TheResult:=ReadAsFunction(FileOutRes)();
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileErr1);
  RemoveFileIfExist(FileErr2);
  RemoveFileIfExist(FileOutRes);
  RemoveFileIfExist(FileMath);
  return TheResult;
end;



#
# Dense matrix in input.
# Translating to sparse matrices
GLPK_LinearProgrammingPlusEqua_General:=function(ListIneq, ListEqua, ToBeMinimized, StrType, RecOpt)
  local nbIneq, ListAconst, ListEntries, nbVar, iIneq, eIneq, eVect, ListIdx, eEnt, ListBconst, nbEqua, iEqua, eEqua, Aspmat, Bspmat;
  nbIneq:=Length(ListIneq);
  ListAconst:=[];
  ListEntries:=[];
  nbVar:=Length(ListIneq[1])-1;
  for iIneq in [1..nbIneq]
  do
    eIneq:=ListIneq[iIneq];
    eVect:=eIneq{[2..nbVar+1]};
    Add(ListAconst, -eIneq[1]);
    ListIdx:=Filtered([1..nbVar], x->eVect[x]<>0);
    eEnt:=rec(ListCol:=ListIdx, ListVal:=eVect{ListIdx});
    Add(ListEntries, eEnt);
  od;
  Aspmat:=rec(nbLine:=nbIneq, nbCol:=nbVar, ListEntries:=ListEntries);
  #
  ListBconst:=[];
  ListEntries:=[];
  nbEqua:=Length(ListEqua);
  for iEqua in [1..nbEqua]
  do
    eEqua:=ListEqua[iEqua];
    eVect:=eEqua{[2..nbVar+1]};
    Add(ListBconst, -eEqua[1]);
    ListIdx:=Filtered([1..nbVar], x->eVect[x]<>0);
    eEnt:=rec(ListCol:=ListIdx, ListVal:=eVect{ListIdx});
    Add(ListEntries, eEnt);
  od;
  Bspmat:=rec(nbLine:=nbEqua, nbCol:=nbVar, ListEntries:=ListEntries);
  #
  return GLPK_LinearProgrammingPlusEqua_General_SparseMat(Aspmat, ListAconst, Bspmat, ListBconst, ToBeMinimized, StrType, RecOpt);
end;




GLPK_LinearProgramming_General:=function(ListIneq, ToBeMinimized, StrType, RecOpt)
  local ListEqua;
  ListEqua:=[];
  return GLPK_LinearProgrammingPlusEqua_General(ListIneq, ListEqua, ToBeMinimized, StrType, RecOpt);
end;






GLPK_LinearProgramming_raw:=function(ListIneq, ToBeMinimized)
  local StrType, ListIneqRed, ToBeMinimizedRed, RecOpt;
  StrType:="rational";
  ListIneqRed:=List(ListIneq, RemoveFraction);
  ToBeMinimizedRed:=RemoveFraction(ToBeMinimized);
  RecOpt:=rec(optimString:="");
  return GLPK_LinearProgramming_General(ListIneqRed, ToBeMinimizedRed, StrType, RecOpt);
end;





GLPK_LinearProgramming:=function(ListIneq, ToBeMinimized)
  local StrType, ListIneqRed, ToBeMinimizedRed, nbIneq, TheRes, NLset, ListIneqSel, NSP, eNSP, TheVert, TheDim, posFirst, eNSPfirst, eFirstPoint, eDiff, ColumnSpace, TheSpace, SEC_ListIneq, SEC_ToBeMinimized, TheLP, eVect, optimal, RecOpt;
  StrType:="rational";
  nbIneq:=Length(ListIneq);
  TheDim:=Length(ListIneq[1]);
  ListIneqRed:=List(ListIneq, RemoveFraction);
  ToBeMinimizedRed:=RemoveFraction(ToBeMinimized);
  RecOpt:=rec(optimString:=" --norelax --tmlim 60");
  TheRes:=GLPK_LinearProgramming_General(ListIneqRed, ToBeMinimizedRed, StrType, RecOpt);
  if TheRes.Status="Undefined" then
    Print("Status=Undefined found Saving TheRes\n");
    SaveDataToFile("TheRes", TheRes);
    return LinearProgramming(ListIneq, ToBeMinimized);
  fi;
  NLset:=Filtered([1..nbIneq], x->TheRes.INEQ_NL[x]=1);
  ListIneqSel:=ListIneq{NLset};
  NSP:=NullspaceMat(TransposedMat(ListIneqSel));
  if Length(NSP)<>1 then
    Print("|NSP|=", Length(NSP), "\n");
    posFirst:=First([1..Length(NSP)], x->NSP[x][1]<>0);
    eNSPfirst:=NSP[posFirst];
    eFirstPoint:=eNSPfirst / eNSPfirst[1];
    eDiff:=Difference([1..Length(NSP)], [posFirst]);
    TheSpace:=List(NSP{eDiff}, x->x - x[1]*eFirstPoint);
    ColumnSpace:=Concatenation([eFirstPoint], TheSpace);
    SEC_ListIneq:=List(ListIneqRed, x->List(ColumnSpace, y->x*y));
    SEC_ToBeMinimized:=List(ColumnSpace, y->y*ToBeMinimized);
    TheLP:=LinearProgramming(SEC_ListIneq, SEC_ToBeMinimized);
    if IsBound(TheLP.TheVert) then
      TheVert:=TheLP.TheVert * ColumnSpace;
    else
      return LinearProgramming(ListIneq, ToBeMinimized);
    fi;
  else
    eNSP:=NSP[1];
    TheVert:=eNSP / eNSP[1];
  fi;
  eVect:=TheVert{[2..TheDim]};
  optimal:=TheVert * ToBeMinimized;
  return rec(method:="glpk", 
             TheVert:=TheVert,
             optimal:=optimal,
             eVect:=eVect);
end;


#
# We check for feasible solution
#
GLPK_LinearProgramming_Secure:=function(ListIneq, ToBeMinimized)
  local TheLP, TheVert, eSetIncd, TheDim, eVectTest, eExpr, LPsol;
  TheLP:=GLPK_LinearProgramming(ListIneq, ToBeMinimized);
  if IsBound(TheLP.primal_direction) or IsBound(TheLP.primal_solution) then
    return TheLP;
  fi;
  if TheLP.method="cdd" then
    return TheLP;
  fi;
  TheVert:=TheLP.TheVert;
  if First(ListIneq, x->x*TheVert<0)<>fail then
    Print("The GLPK does not return a feasible solution\n");
    Print("Plan B: Running with the CDD, 1\n");
    return LinearProgramming(ListIneq, ToBeMinimized);
  fi;
  eSetIncd:=Filtered([1..Length(ListIneq)], x->ListIneq[x]*TheVert=0);
  TheDim:=Length(ToBeMinimized);
  eVectTest:=Concatenation([ToBeMinimized[1]-TheLP.optimal], ToBeMinimized{[2..TheDim]});
  eExpr:=SolutionMatNonnegative(ListIneq{eSetIncd}, eVectTest);
  if eExpr=fail then
    Print("The GLPK does not return a feasible solution\n");
    Print("Plan B: Running with the CDD, 2\n");
    LPsol:=LinearProgramming(ListIneq, ToBeMinimized);
    Print("LPsol=", LPsol, "\n");
    Print("ListIneq=", ListIneq, "\n");
    SaveDataToFile("TheLinearProgram", rec(ListIneq:=ListIneq, ToBeMinimized:=ToBeMinimized));
    return LPsol;
  fi;
  return TheLP;
end;




GLPK_IntegerLinearProgramming:=function(ListIneq, ToBeMinimized)
  local TheLP1, TheLP2, StrType, RecOpt;
  #
  # First try standard linear programming. If not feasible, then return it.
  #
  TheLP1:=GLPK_LinearProgramming_Secure(ListIneq, ToBeMinimized);
  if IsBound(TheLP1.optimal)=false then
    return TheLP1;
  fi;
  #
  # Now try the ILP.
  #
  StrType:="integer";
  RecOpt:=rec(optimString:="");
  TheLP2:=GLPK_LinearProgramming_General(ListIneq, ToBeMinimized, StrType, RecOpt);
  if IsBound(TheLP2.Objective) then
    TheLP2.optimal:=TheLP2.Objective;
  fi;
  if IsBound(TheLP2.eVect) then
    TheLP2.TheVert:=Concatenation([1], TheLP2.eVect);
  fi;
#  Print(NullMat(5));
  return TheLP2;
end;






LPSOLVE_LinearProgramming:=function(ListIneq, ToBeMinimized)
  local FileIn, FileOut, FileRes, FileErr, nbVar, nbIneq, output, iVar, eVal, StrAdd, iIneq, eIneq, eDiff, eConst, TheResult, ListIneqRed, ToBeMinimizedRed;
  SaveDataToFile("ExampleLP", rec(ListIneq:=ListIneq, ToBeMinimized:=ToBeMinimized));
  ListIneqRed:=List(ListIneq, RemoveFraction);
  ToBeMinimizedRed:=RemoveFraction(ToBeMinimized);
  FileIn:=Filename(POLYHEDRAL_tmpdir, "LPSOLVE.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "LPSOLVE.out");
  FileRes:=Filename(POLYHEDRAL_tmpdir, "LPSOLVE.res");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "LPSOLVE.err");
  RemoveFileIfExist(FileRes);
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOut);

  nbVar:=Length(ToBeMinimizedRed)-1;
  nbIneq:=Length(ListIneqRed);
#  Print("nbVar=", nbVar, "  nbIneq=", nbIneq, "\n");
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, "min: ");
  for iVar in [1..nbVar]
  do
    eVal:=ToBeMinimizedRed[iVar+1];
    if eVal<>0 then
      if eVal > 0 then
        StrAdd:="+";
      else
        StrAdd:="";
      fi;
      AppendTo(output, StrAdd, String(eVal), " X", String(iVar), " ");
    else
      AppendTo(output, "+0 X", String(iVar), " ");
    fi;
  od;
  AppendTo(output, ";\n");
  AppendTo(output, "\n");
  #
  for iIneq in [1..nbIneq]
  do
    eIneq:=ListIneqRed[iIneq];
    eConst:=eIneq[1];
    eDiff:=-eIneq{[2..nbVar+1]};
    AppendTo(output, "row", iIneq, ": ");
    for iVar in [1..nbVar]
    do
      eVal:=eDiff[iVar];
      if eVal<>0 then
        if eVal>0 then
          StrAdd:="+";
        else
          StrAdd:="";
        fi;
        AppendTo(output, StrAdd, eVal, " X", iVar, " ");
      fi;
    od;
    AppendTo(output, "<= ", eConst, ";\n");
  od;
  AppendTo(output, "\n");
  AppendTo(output, "free");
  for iVar in [1..nbVar]
  do
    if iVar> 1 then
      AppendTo(output, ",");
    fi;
    AppendTo(output, " X", String(iVar));
  od;
  AppendTo(output, ";\n");
  #
  # Now running the program
  #
  Exec(FileLpsolve, " ", FileIn, " > ", FileOut, " 2>", FileErr);
  if IsEmptyFile(FileErr)=false then
    Error("Nonempty error file in Call to LPSOLVE");
  fi;
  Exec(FileLpsolveExtractSolution, " ", FileOut, " > ", FileRes);
  #
  #
  #
  TheResult:=ReadAsFunction(FileRes)();
  RemoveFileIfExist(FileRes);
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOut);
  return TheResult;
end;



# Least square solution
# We want |x0 + zK|^2 minimal
# So, if we have
# (x0 + zK) D K^T deltaz = 0
# So the system is
# x0 D K^T = -z [KDK^T]
GetBestSolution_L2:=function(ListXweight, TheMat, TheVect)
  local x0, TheKer, dimKer, dimX, dimB, DiagMat, i, TheProd, bSide, z, SolX;
  x0:=SolutionMat(TheMat, TheVect);
  if x0=fail then
    return fail;
  fi;
  TheKer:=NullspaceMat(TheMat);
  dimKer:=Length(TheKer);
  dimX:=Length(TheMat);
  dimB:=Length(TheVect);
  if Length(TheKer)=0 then
    return x0;
  fi;
  DiagMat:=NullMat(dimX, dimX);
  for i in [1..dimX]
  do
    DiagMat[i][i]:=1/ListXweight[i];
  od;
  TheProd:=-TheKer*DiagMat*TransposedMat(TheKer);
  bSide:=x0*DiagMat*TransposedMat(TheKer);
  z:=bSide*Inverse(TheProd);
  SolX:=x0 + z*TheKer;
  return SolX;
end;


Norm_L1:=function(eVect)
  return Sum(List(eVect, AbsInt));
end;

Norm_L0:=function(eVect)
  return Length(Filtered(eVect, x->x<>0));
end;



#
# We want to find smallest L1 solution of 
# xA = B
# Solution is of the form X0 + z K
# We want to minimize sum_i |x_i| / w_i
# On each X coordinates we write
# So, for each i we have the inequalities
# x_i <= w_i d_i and -x_i <= w_i d_i
# the function to be minimized is
# sum d_i
# total number of variables is dimKer + dimX
#
# For Linfinity, we want to minimize
# Max_i |x_i| / w_i
# So we have the inequalities
# x_i <= w_i d and -x_i <= w_i d
# and we minimize
# d
# number of variables is dimKer + 1
GetBestSolution_L1_version1:=function(ListXweight, TheMat, TheVect, UseGLPK)
  local x0, TheKer, dimKer, dimX, dimB, ListIneq, eVect1, eVect2, i, j, ToBeMinimized, TheLP, z, eEnt, SolX, TotSol, ListIneqRed, ToBeMinimizedRed, ListRelevant, eSetRelevant, TheLP_glpk;
  dimX:=Length(TheMat);
  dimB:=Length(TheVect);
  if Norm_L1(TheVect)=0 then
    return ListWithIdenticalEntries(Length(TheMat), 0);
  fi;
#  Print("V1: dimX=", dimX, " dimB=", dimB, "\n");
  x0:=SolutionMat(TheMat, TheVect);
  if x0=fail then
    return fail;
  fi;
  TheKer:=NullspaceMat(TheMat);
  dimKer:=Length(TheKer);
  if Length(TheKer)=0 then
    return x0;
  fi;
  ListIneq:=[];
  for i in [1..dimX]
  do
    eVect1:=ListWithIdenticalEntries(1 + dimKer + dimX, 0);
    eVect2:=ListWithIdenticalEntries(1 + dimKer + dimX, 0);
    eVect1[1]:=-x0[i];
    eVect2[1]:= x0[i];
    for j in [1..dimKer]
    do
      eVect1[1+j]:=-TheKer[j][i];
      eVect2[1+j]:= TheKer[j][i];
    od;
    eVect1[1+dimKer+i]:=ListXweight[i];
    eVect2[1+dimKer+i]:=ListXweight[i];
    Add(ListIneq, eVect1);
    Add(ListIneq, eVect2);
  od;
  ToBeMinimized:=ListWithIdenticalEntries(1 + dimKer + dimX, 0);
  for i in [1..dimX]
  do
    ToBeMinimized[1+dimKer+i]:=1;
  od;
  UseGLPK:=true;
  if UseGLPK then
    TheLP_glpk:=GLPK_LinearProgramming_raw(ListIneq, ToBeMinimized);
    ListRelevant:=Filtered([1..dimKer+dimX], x->TheLP_glpk.NearZero[x]=0);
  else
    ListRelevant:=[1..dimKer+dimX];
  fi;
  eSetRelevant:=Concatenation([1], List(ListRelevant, x->x+1));
  ListIneqRed:=List(ListIneq, x->x{eSetRelevant});
  ToBeMinimizedRed:=ToBeMinimized{eSetRelevant};
  TheLP:=LinearProgramming(ListIneqRed, ToBeMinimizedRed);
  TotSol:=ListWithIdenticalEntries(dimKer+dimX, 0);
  TotSol{ListRelevant}:=TheLP.eVect;
  z:=TotSol{[1..dimKer]};
  SolX:=x0 + z*TheKer;
  return SolX;
end;


GetBestSolution_L1_version2_subset:=function(ListXweight, TheMat, TheVect, eSetRelevant)
  local dimX, dimB, TheMatRed, iLine, iRel, eEnt, i, iCol, eVal, ListXweightRed, UseGLPK, TheSolRed, TheSol;
  #
  dimX:=TheMat.nbLine;
  dimB:=Length(TheVect);
  TheMatRed:=NullMat(Length(eSetRelevant), dimB);
  for iLine in [1..Length(eSetRelevant)]
  do
    iRel:=eSetRelevant[iLine];
    eEnt:=TheMat.ListEntries[iRel];
    for i in [1..Length(eEnt.ListVal)]
    do
      iCol:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      TheMatRed[iLine][iCol]:=eVal;
    od;
  od;
  ListXweightRed:=ListXweight{eSetRelevant};
  UseGLPK:=false;
  TheSolRed:=GetBestSolution_L1_version1(ListXweightRed, TheMatRed, TheVect, UseGLPK);
  if TheSolRed=fail then
    return fail;
  fi;
  TheSol:=ListWithIdenticalEntries(dimX,0);
  TheSol{eSetRelevant}:=TheSolRed;
  return TheSol;
end;




GetBestSolution_L1_version2:=function(ListXweight, TheMat, TheVect)
  local dimKer, dimX, dimB, ListIneq, eVect1, eVect2, i, j, ToBeMinimized, TheLP, z, eEnt, SolX, TotSol, ListIneqRed, ToBeMinimizedRed, eSetRelevant, UseGLPK, TheLP_glpk, ListEqua, eEqua, TheSolRed, ListXweightRed, StrType, TheSol, TheMatRed, ListAconst, ListBconst, eEnt1, eEnt2, ListEntries, iLine, Aspmat, Bspmat, iRel, iCol, eVal, RecOpt;
  dimX:=TheMat.nbLine;
  dimB:=Length(TheVect);
  if TheMat.nbCol<>dimB then
    Error("Wrong input matrices");
  fi;
#  Print("V2: dimX=", dimX, " dimB=", dimB, "\n");
  if Norm_L1(TheVect)=0 then
    return ListWithIdenticalEntries(dimX, 0);
  fi;
  ListAconst:=[];
  ListEntries:=[];
  ListIneq:=[];
  for i in [1..dimX]
  do
    eEnt1:=rec(ListCol:=[i,i+dimX], ListVal:=[-1,ListXweight[i]]);
    eEnt2:=rec(ListCol:=[i,i+dimX], ListVal:=[ 1,ListXweight[i]]);
    Add(ListEntries, eEnt1);
    Add(ListEntries, eEnt2);
    Add(ListAconst, 0);
    Add(ListAconst, 0);
  od;
  Aspmat:=rec(nbLine:=2*dimX, nbCol:=2*dimX, ListEntries:=ListEntries);
  ToBeMinimized:=ListWithIdenticalEntries(1 + dimX + dimX, 0);
  for i in [1..dimX]
  do
    ToBeMinimized[1+dimX+i]:=1;
  od;
  ListEqua:=[];
  ListEntries:=[];
  for i in [1..dimB]
  do
    Add(ListEntries, rec(ListCol:=[], ListVal:=[]));
  od;
  for iLine in [1..dimX]
  do
    eEnt:=TheMat.ListEntries[iLine];
    for i in [1..Length(eEnt.ListVal)]
    do
      iCol:=eEnt.ListCol[i];
      eVal:=eEnt.ListVal[i];
      Add(ListEntries[iCol].ListVal, eVal);
      Add(ListEntries[iCol].ListCol, iLine);
    od;
  od;
  Bspmat:=rec(nbLine:=dimB, nbCol:=2*dimX, ListEntries:=ListEntries);
  ListBconst:=TheVect;
  StrType:="rational";
  RecOpt:=rec(optimString:="");
  TheLP_glpk:=GLPK_LinearProgrammingPlusEqua_General_SparseMat(Aspmat, ListAconst, Bspmat, ListBconst, ToBeMinimized, StrType, RecOpt);
  if TheLP_glpk.Status="Undefined" then
    return fail;
  fi;
  eSetRelevant:=Filtered([1..dimX], x->TheLP_glpk.NearZero[x]=0);
  #
  return GetBestSolution_L1_version2_subset(ListXweight, TheMat, TheVect, eSetRelevant);
end;




GetAMPSolution_ListNonZero:=function(TheMat, TheVect)
  local FileSpMat, FileVect, FileOut, TheRes;
  FileSpMat:=Filename(POLYHEDRAL_tmpdir,"AMP_solver_spmat");
  FileVect:=Filename(POLYHEDRAL_tmpdir,"AMP_solver_vect");
  FileOut:=Filename(POLYHEDRAL_tmpdir,"AMP_solver_out");
#  Print("FileSpMat=", FileSpMat, "\n");
#  Print("FileVect=", FileVect, "\n");
#  Print("FileOut=", FileOut, "\n");
  RemoveFileIfExist(FileSpMat);
  RemoveFileIfExist(FileVect);
  RemoveFileIfExist(FileOut);
  CPP_PrintSparseMatrix(FileSpMat, TheMat);
  CPP_PrintVector(FileVect, TheVect);
  #
  Exec(FileStandaloneSparseSolver_NNZ, " ", FileSpMat, " ", FileVect, " ", FileOut);
  #
  TheRes:=ReadAsFunction(FileOut)();
  RemoveFileIfExist(FileSpMat);
  RemoveFileIfExist(FileVect);
  RemoveFileIfExist(FileOut);
  return TheRes;
end;


GetAMPSparseSolution:=function(TheMat, TheVect)
  local ListIdx, LIdx, nbLine, nbCol, ListXweight, TheSol, FileSave;
  ListIdx:=GetAMPSolution_ListNonZero(TheMat, TheVect);
  LIdx:=Filtered([1..Length(ListIdx)], x->ListIdx[x]=1);
  Print("|LIdx|=", Length(LIdx), "\n");
  if Length(LIdx)>1000 then
    Print("Too large vector. It would certainly fail\n");
    return fail;
  fi;
  nbLine:=TheMat.nbLine;
  nbCol:=TheMat.nbCol;
  Print("nbLine=", nbLine, " nbCol=", nbCol, "\n");
  ListXweight:=ListWithIdenticalEntries(nbLine,1);
  TheSol:=GetBestSolution_L1_version2_subset(ListXweight, TheMat, TheVect, LIdx);
  if TheSol=fail then
#    FileSave:=Concatenation("CASE_STUDY_", String(nbLine), "_", String(nbCol));
#    SaveDataToFile(FileSave, rec(TheMat:=TheMat, TheVect:=TheVect));
#    Print("AMP strategy failed. Trying classic GLPK\n");
#    return GetBestSolution_L1_version2(ListXweight, TheMat, TheVect);
    Print("AMP strategy failed. We assumed LP would fail as well\n");
    return fail;
  fi;
  return TheSol;
end;






GetBestSolution_Linfinity:=function(ListXweight, TheMat, TheVect)
  local x0, TheKer, dimKer, dimX, dimB, ListIneq, i, eVect1, eVect2, j, ToBeMinimized, TheLP, z, eEnt, SolX;
  x0:=SolutionMat(TheMat, TheVect);
  if x0=fail then
    return fail;
  fi;
  TheKer:=NullspaceMat(TheMat);
  dimKer:=Length(TheKer);
  dimX:=Length(TheMat);
  dimB:=Length(TheVect);
  if Length(TheKer)=0 then
    return x0;
  fi;
  ListIneq:=[];
  for i in [1..dimX]
  do
    eVect1:=ListWithIdenticalEntries(1 + dimKer + 1, 0);
    eVect2:=ListWithIdenticalEntries(1 + dimKer + 1, 0);
    eVect1[1]:=-x0[i];
    eVect2[1]:= x0[i];
    for j in [1..dimKer]
    do
      eVect1[1+j]:=-TheKer[j][i];
      eVect2[1+j]:= TheKer[j][i];
    od;
    eVect1[1+dimKer+1]:=ListXweight[i];
    eVect2[1+dimKer+1]:=ListXweight[i];
    Add(ListIneq, eVect1);
    Add(ListIneq, eVect2);
  od;
  ToBeMinimized:=ListWithIdenticalEntries(1 + dimKer + dimX, 0);
  ToBeMinimized[1+dimKer+1]:=1;
  TheLP:=LinearProgramming(ListIneq, ToBeMinimized);
  z:=TheLP.eVect{[1..dimKer]};
  SolX:=x0 + z*TheKer;
  return SolX;
end;


FractionalChromaticNumber:=function(GRA)
  local GRP, nbV, GRAcompl, ListIndepTot, siz, ListIndep, Oset, nbOset, ToBeMinimized, iO, ListIneq, eVect, Opt, eOpt, ePt, ListSubSet, TheRes, ListOrbSizes, eStab, OrbSiz, nbCont, eX, TotalIncidence, ptIncd;
  nbV:=GRA.order;
  GRP:=GRA.group;
  Print("FractionalChromaticNumber nbV=", nbV, " |GRP|=", Order(GRP), "\n");
  GRAcompl:=ComplementGraph(GRA);
  ListIndepTot:=[];
  siz:=1;
  while(true)
  do
    ListIndep:=CompleteSubgraphsOfGivenSize(GRAcompl, siz);
    Print("siz=", siz, " |ListIndep|=", Length(ListIndep), "\n");
    if Length(ListIndep)=0 then
      break;
    fi;
    Append(ListIndepTot, ListIndep);
    siz:=siz+1;
  od;
  nbOset:=Length(ListIndepTot);
  Print("nbOset=", nbOset, "\n");
  ToBeMinimized:=ListWithIdenticalEntries(1+nbOset, 0);
  ListOrbSizes:=[];
  for iO in [1..nbOset]
  do
    eStab:=Stabilizer(GRP, ListIndepTot[iO], OnSets);
    OrbSiz:=Order(GRP) / Order(eStab);
    Add(ListOrbSizes, OrbSiz);
    ToBeMinimized[iO+1]:=OrbSiz;
  od;
  Print("We have ToBeMinimized\n");
  ListIneq:=[];
  for iO in [1..nbOset]
  do
    eVect:=ListWithIdenticalEntries(1+nbOset, 0);
    eVect[iO+1]:=1;
    Add(ListIneq, eVect);
  od;
  Opt:=Orbits(GRP, [1..nbV], OnPoints);
  for eOpt in Opt
  do
    ePt:=eOpt[1];
    eVect:=ListWithIdenticalEntries(1+nbOset, 0);
    eVect[1]:=-1;
    for iO in [1..nbOset]
    do
      OrbSiz:=ListOrbSizes[iO];
      nbCont:=0;
      for eX in ListIndepTot[iO]
      do
        if Position(eOpt, eX)<>fail then
	  nbCont:=nbCont+1;
	fi;
      od;
      TotalIncidence:=nbCont*OrbSiz;
      ptIncd:=TotalIncidence / Length(eOpt);
      if IsInt(ptIncd)=false then
        Error("We do not have consistency");
      fi;
      eVect[1+iO]:=ptIncd;
    od;
    Add(ListIneq, eVect);
  od;
  Print("Linear program has been formed\n");
  TheRes:=GLPK_LinearProgramming_Secure(ListIneq, ToBeMinimized);
#  TheRes:=LinearProgramming_Rational(ListIneq, ToBeMinimized);
#  Print(NullMat(5));
  return TheRes;
end;



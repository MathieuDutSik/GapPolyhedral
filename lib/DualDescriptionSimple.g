FileRemoveFractions:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"removeFractions");
FileGLRS:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"glrs");
FileIsoReduction:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"IsomorphismReduction.prog");
FileNudifyLRS:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NudifyLRS");
FileSCDD:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"scdd_gmp");
FileLCDD:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"lcdd_gmp");
FilePPL_LCDD:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ppl_lcdd");
FileNudify:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Nudify");
FileCddToNauty:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"CddToNauty");
FileNudifyLRS_reduction:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NudifyLRS.reduction");
FileNudifyCDD_reduction:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NudifyCDD.reduction");
FileNautyToGRAPE:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NautyToGRAPE");




OutputGroup:=function(GroupExt, nbExt, FileGroup)
  local output, ListGens, nbGen, eGen, eList, i;
  ListGens:=GeneratorsOfGroup(GroupExt);
  nbGen:=Length(ListGens);
  output:=OutputTextFile(FileGroup, true);;
  AppendTo(output, nbExt, " ", nbGen, "\n");
  for eGen in ListGens
  do
    eList:=OnTuples([1..nbExt], eGen);
    for i in [1..nbExt]
    do
      AppendTo(output, " ", eList[i]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;



#
#
# Pass from one description to the other using RAW cdd program
DualDescription_Rational:=function(EXT)
  local FileExt, FileIne, FileIneNude, output, FAC, FileErr, EXTred;
  if Length(Set(List(EXT,Length)))<>1 then
    Error("DualDescription_Rational: Input should be vectors of the same length");
  fi;
  if RankMat(EXT)<>Length(EXT[1]) then
    Print("DualDescription_Rational: The rank is not correct\n");
    Print("| EXT[1] |=", Length(EXT[1]), "  rnk=", RankMat(EXT), "\n");
    Error("Please correct");
  fi;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.ext");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.err");
  FileIne:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.ine");
  FileIneNude:=Filename(POLYHEDRAL_tmpdir,"CDD_Desc.ine.Nude"); 
  RemoveFileIfExist(FileExt);
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileLCDD, " ", FileExt, " > ", FileIne, " 2> ", FileErr);
  Exec(FileNudify, " ", FileIne," > ", FileIneNude);
  FAC:=List(ReadVectorFile(FileIneNude), RemoveFraction);
  if Length(FAC)=0 then
    Error("FAC is empty");
  fi;
  RemoveFile(FileExt);
  RemoveFile(FileErr);
  RemoveFile(FileIne);
  RemoveFile(FileIneNude);
  return FAC;
end;



DualDescription_General_Code:=function(EXT)
  local Nval;
  if IsMatrixRational(EXT)=true then
    return DualDescription_Rational(EXT);
  fi;
  Error("You have to build your own arithmetic");
end;


DualDescription:=function(EXT)
  if IsMatrixRational(EXT)=true then
    return DualDescription_Rational(EXT);
  fi;
  Print("Need to put arithmetic or use DualDescriptionGeneralCode\n");
  Error("You have to build your own arithmetic");
end;


EliminationByRedundancyDualDescription:=function(FAC)
  local FACred, EXTred, TheRank, FACreturn, nbFac, iFac, eFac, eFacRed, LINC, eEXT;
  FACred:=ColumnReduction(FAC).EXT;
  EXTred:=DualDescription(FACred);
  TheRank:=Length(FACred[1]);
  FACreturn:=[];
  nbFac:=Length(FACred);
  for iFac in [1..nbFac]
  do
    eFac:=FAC[iFac];
    eFacRed:=FACred[iFac];
    LINC:=[];
    for eEXT in EXTred
    do
      if eEXT*eFacRed=0 then
        Add(LINC, eEXT);
      fi;
    od;
    if PersoRankMat(LINC)=TheRank-1 then
      Add(FACreturn, eFac);
    fi;
  od;
  return FACreturn;
end;




DualDescriptionSets:=function(EXT)
  local eSelect, EXTproj, FACproj;
  eSelect:=ColumnReduction(EXT).Select;
  EXTproj:=List(EXT, x->x{eSelect});
  FACproj:=DualDescription(EXTproj);
  return List(FACproj, x->Filtered([1..Length(EXTproj)], y->EXTproj[y]*x=0));
end;

RemoveRedundancyByDualDescription_Kernel:=function(EXT)
  local eSelect, EXTproj, FACproj, eSet, len, idx, FACinc;
  if Length(EXT)=1 then
    return EXT;
  fi;
  eSelect:=ColumnReduction(EXT).Select;
  EXTproj:=List(EXT, x->RemoveFraction(x{eSelect}));
  len:=Length(EXTproj[1]);
  FACproj:=DualDescription(EXTproj);
  eSet:=[];
  for idx in [1..Length(EXTproj)]
  do
    FACinc:=Filtered(FACproj, x->x*EXTproj[idx]=0);
    if Length(FACinc)>0 then
      if RankMat(FACinc)=len-1 then
        Add(eSet, idx);
      fi;
    fi;
  od;
  return Set(EXT{eSet});
end;

RemoveRedundancyByDualDescription:=function(EXT0)
  local EXT1, EXT2, EXT3;
  EXT1:=Filtered(EXT0, x->x*x>0);
  EXT2:=List(EXT1, RemoveFraction);
  EXT3:=Set(EXT2);
  return RemoveRedundancyByDualDescription_Kernel(EXT3);
end;


WriteCddInputVertices:=function(FileName, EXT)
  local output;
  output:=OutputTextFile(FileName, true);
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  CloseStream(output);
end;



DualDescriptionAdjacencies:=function(EXT)
  local FileExt, FileIne, FileLog, FileErr, FileDdl, FileIneNude, FileIad, FileEad, FileIadNauty, FileEadNauty, FileIadGrape, FileEadGrape, output, RidgeGraph, SkeletonGraph, FAC;
  FileExt:=Filename(POLYHEDRAL_tmpdir,"Desc.ext");
  FileIne:=Filename(POLYHEDRAL_tmpdir,"Desc.ine");
  FileLog:=Filename(POLYHEDRAL_tmpdir,"Desc.log");
  FileErr:=Filename(POLYHEDRAL_tmpdir,"Desc.err");
  FileIneNude:=Filename(POLYHEDRAL_tmpdir,"Desc.ine.Nude");
  FileIad:=Filename(POLYHEDRAL_tmpdir,"Desc.iad");
  FileEad:=Filename(POLYHEDRAL_tmpdir,"Desc.ead");
  FileDdl:=Filename(POLYHEDRAL_tmpdir,"Desc.ddl");
  FileIadNauty:=Filename(POLYHEDRAL_tmpdir,"Desc.iad.nauty");
  FileEadNauty:=Filename(POLYHEDRAL_tmpdir,"Desc.ead.nauty");
  FileIadGrape:=Filename(POLYHEDRAL_tmpdir,"Desc.iad.grape");
  FileEadGrape:=Filename(POLYHEDRAL_tmpdir,"Desc.ead.grape");
  output:=OutputTextFile(FileExt, true);;
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), "  ", Length(EXT[1]), "  integer\n");
  WriteMatrix(output, EXT);
  AppendTo(output, "end\n");
  AppendTo(output, "adjacency\n");
  AppendTo(output, "input_adjacency\n");
  CloseStream(output);
  Exec(FileSCDD, " ", FileExt, " > ", FileLog, " 2> ", FileErr);
#  Exec(FileSCDD, " ", FileExt);
  Exec(FileNudify, " ", FileIne," > ", FileIneNude);
  Exec(FileCddToNauty, " ", FileIad, " > ", FileIadNauty);
  Exec(FileNautyToGRAPE, " ", FileIadNauty, " > ", FileIadGrape);
  RidgeGraph:=ReadAsFunction(FileIadGrape)();
  Exec(FileCddToNauty, " ", FileEad, " > ", FileEadNauty);
  Exec(FileNautyToGRAPE, " ", FileEadNauty, " > ", FileEadGrape);
  SkeletonGraph:=ReadAsFunction(FileEadGrape)();
  FAC:=List(ReadVectorFile(FileIneNude), RemoveFraction);
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  RemoveFile(FileLog);
  RemoveFile(FileErr);
  RemoveFile(FileDdl);
  RemoveFile(FileIneNude);
  RemoveFile(FileIad);
  RemoveFile(FileEad);
  RemoveFile(FileIadNauty);
  RemoveFile(FileEadNauty);
  RemoveFile(FileIadGrape);
  RemoveFile(FileEadGrape);
  if Length(FAC)=0 then
    Error("Error in DualDescriptionAdjacencies");
  fi;
  return rec(FAC:=FAC, SkeletonGraph:=SkeletonGraph, RidgeGraph:=RidgeGraph);
end;


__DualDescriptionCDD_QN:=function(Nval, EXT, GroupExt, ThePath)
  local FileExt, FileIne, FileLog, FileDdl, FileIneNude, output, LPFAC, RPL, eFac, ePair, eSub, EXT2, EXTnew, eVal, DimEXT, eEXT, FAC2, eVect, eNewVect, NvalueFile;
#  Print("Entering polyhedral function CDD QN Nval=", Nval, " |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath,"CDD_Project_QN.ext");
  FileIne:=Concatenation(ThePath,"CDD_Project_QN.ine");
  FileLog:=Concatenation(ThePath,"CDD_Project_QN.log");
  FileDdl:=Concatenation(ThePath,"CDD_Project_QN.ddl");
  FileIneNude:=Filename(POLYHEDRAL_tmpdir,"CDD_Project_QN.ine.Nude");
  #
  NvalueFile:="/tmp/InitialN";
  RemoveFileIfExist(NvalueFile);
  output:=OutputTextFile(NvalueFile, true);;
  AppendTo(output, " ", Nval, "\n");
  CloseStream(output);
  #
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  if TestConicness(EXT2) then
    EXTnew:=ShallowCopy(EXT2);
  else
    EXTnew:=List(EXT2, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  WriteMatrixQN(Nval, FileExt, EXTnew);
  Exec(FileLCDD_QN, " ", FileExt, " 2> ", FileLog, " > ", FileIne);
  Exec(FileNudify, " ", FileIne, " > ", FileIneNude);
  LPFAC:=ReadVectorFile(FileIneNude);
  FAC2:=[];
  for eVect in LPFAC
  do
    eNewVect:=List([1..DimEXT], x->eVect[2*x-1] + Sqrt(Nval)*eVect[2*x]);
    Add(FAC2, eNewVect);
  od;
  if Length(FAC2)=0 then
    Error("Error in __DualDescriptionCDD_QN");
  fi;
  RemoveFile(FileExt);
  RemoveFile(FileIne);
  RemoveFile(FileLog);
  RemoveFile(FileDdl);
  RemoveFile(FileIneNude);
  RPL:=OnSetsGroupFormalism(500).OrbitGroupFormalism(EXTnew, GroupExt, "/irrelevant/", false);
  for eFac in FAC2
  do
    RPL.FuncInsert(Filtered([1..Length(EXTnew)], x->EXTnew[x]*eFac=0));
  od;
  return RPL.FuncListOrbitIncidence();
end;


__DualDescriptionLRS_Reduction:=function(EXT, GroupExt, ThePath)
  local eSub, EXT2, EXT3, FileExt, FileOut, FileData, FileGroup, FileMetaData, FileSupport, FileScratch, FileOutput, FileError, output, DimEXT, test, EXTnew, ListInc;
#  Print("Entering polyhedral function LRS_Reduction |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath, "LRS_Project.ext");
  FileOut:=Concatenation(ThePath, "LRS_Project.out");
  FileData:=Concatenation(ThePath, "LRS_Project.data");
  FileGroup:=Concatenation(ThePath, "LRS_Project.group");
  FileMetaData:=Concatenation(ThePath, "LRS_Project.meta");
  FileSupport:=Concatenation(ThePath, "LRS_Project.supo");
  FileScratch:=Concatenation(ThePath, "LRS_Project.scratch");
  FileOutput:=Concatenation(ThePath, "LRS_Project.output");
  FileError:=Concatenation(ThePath, "LRS_Project.error");
  RemoveFileIfExist(FileExt);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileData);
  RemoveFileIfExist(FileGroup);
  RemoveFileIfExist(FileMetaData);
  RemoveFileIfExist(FileSupport);
  RemoveFileIfExist(FileScratch);
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileError);
  #
  output:=OutputTextFile(FileExt, true);
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  EXT3:=List(EXT2, RemoveFraction);
  if TestConicness(EXT3) then
    EXTnew:=ShallowCopy(EXT3);
  else
    EXTnew:=List(EXT3, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  Exec(FileGLRS, " ", FileExt, " > ", FileOut);
  Exec(FileNudifyLRS_reduction, " ", FileData, " ", FileMetaData, " < ", FileOut);
  #
  output:=OutputTextFile(FileSupport, true);
  WriteMatrix(output, EXTnew);
  CloseStream(output);
  #
  OutputGroup(GroupExt, Length(EXTnew), FileGroup);
  #
  Exec(FileIsoReduction, " ", FileData, " ", FileMetaData, " ", FileGroup, " ", FileSupport, " ", FileScratch, " ", FileOutput, "2>", FileError);
  ListInc:=ReadAsFunction(FileOutput)();
  if Length(ListInc)=0 then
    Error("Error in DualDescriptionLRS_Reduction");
  fi;
  RemoveFile(FileExt);
  RemoveFile(FileOut);
  RemoveFile(FileData);
  RemoveFile(FileGroup);
  RemoveFile(FileMetaData);
  RemoveFile(FileSupport);
  RemoveFile(FileScratch);
  RemoveFile(FileOutput);
  RemoveFile(FileError);
  return ListInc;
end;


DualDescriptionLRS:=function(EXT, GroupExt)
  local ThePath;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  return __DualDescriptionLRS_Reduction(EXT, GroupExt, ThePath);
end;




__DualDescriptionDoubleDescMethod_Reduction:=function(EXT, GroupExt, ThePath, TheProg)
  local eSub, EXT2, FileExt, FileOut, FileData, FileGroup, FileMetaData, FileSupport, FileScratch, FileOutput, output, DimEXT, test, EXTnew, ListInc, FileDataPre, FileError, TheCommand;
#  Print("Entering polyhedral function CDD_Reduction |GRP|=", Order(GroupExt), "\n");
  FileExt:=Concatenation(ThePath, "DD_Project.ext");
  FileOut:=Concatenation(ThePath, "DD_Project.out");
  FileDataPre:=Concatenation(ThePath, "DD_Project.datapre");
  FileData:=Concatenation(ThePath, "DD_Project.data");
  FileGroup:=Concatenation(ThePath, "DD_Project.group");
  FileMetaData:=Concatenation(ThePath, "DD_Project.meta");
  FileSupport:=Concatenation(ThePath, "DD_Project.supo");
  FileScratch:=Concatenation(ThePath, "DD_Project.scratch");
  FileOutput:=Concatenation(ThePath, "DD_Project.output");
  FileError:=Concatenation(ThePath, "DD_Project.error");
  RemoveFileIfExist(FileExt);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileDataPre);
  RemoveFileIfExist(FileData);
  RemoveFileIfExist(FileGroup);
  RemoveFileIfExist(FileMetaData);
  RemoveFileIfExist(FileSupport);
  RemoveFileIfExist(FileScratch);
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileError);
  #
  output:=OutputTextFile(FileExt, true);;
  eSub:=__ProjectionFrame(EXT);
  EXT2:=List(EXT, x->x{eSub});
  if TestConicness(EXT2) then
    EXTnew:=ShallowCopy(EXT2);
  else
    EXTnew:=List(EXT2, x->Concatenation([0], x));
  fi;
  DimEXT:=Length(EXTnew[1]);
  #
  AppendTo(output, "V-representation\n");
  AppendTo(output, "begin\n");
  AppendTo(output, Length(EXT), " ", DimEXT, " integer\n");
  WriteMatrix(output, EXTnew);
  AppendTo(output, "end\n");
  CloseStream(output);
  #
  if TheProg<>"CDD" and TheProg<>"PPL" then
    Error("TheProg should be CDD or PPL");
  fi;
  if TheProg="CDD" then
    TheCommand:=Concatenation(FileLCDD, " ", FileExt, " > ", FileOut);
  fi;
  if TheProg="PPL" then
    TheCommand:=Concatenation(FilePPL_LCDD, " ", FileExt, " > ", FileOut);
  fi;
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileNudifyCDD_reduction, " ", FileDataPre, " ", FileMetaData, " < ", FileOut);
  Exec(TheCommand);
  Print("Double description computation finished\n");
  #
  TheCommand:=Concatenation(FileRemoveFractions, " < ", FileDataPre, " > ", FileData);
  Exec(TheCommand);
  Print("Operation remove fraction finished\n");
  #
  output:=OutputTextFile(FileSupport, true);
  WriteMatrix(output, EXTnew);
  CloseStream(output);
  #
  OutputGroup(GroupExt, Length(EXTnew), FileGroup);
  #
  TheCommand:=Concatenation(FileIsoReduction, " ", FileData, " ", FileMetaData, " ", FileGroup, " ", FileSupport, " ", FileScratch, " ", FileOutput, " 2>", FileError);
#  Print("TheCommand=", TheCommand, "\n");
  Exec(TheCommand);
  ListInc:=ReadAsFunction(FileOutput)();
  if Length(ListInc)=0 then
    Error("Error in DualDescriptionCDD_Reduction");
  fi;
  Print("Isomorphy reduction finished\n");
#  Print(NullMat(5));
  RemoveFile(FileExt);
  RemoveFile(FileOut);
  RemoveFile(FileDataPre);
  RemoveFile(FileData);
  RemoveFile(FileGroup);
  RemoveFile(FileMetaData);
  RemoveFile(FileSupport);
  RemoveFile(FileScratch);
  RemoveFile(FileOutput);
  RemoveFile(FileError);
  return ListInc;
end;





__DualDescriptionCDD_Reduction:=function(EXT, GroupExt, ThePath)
  return __DualDescriptionDoubleDescMethod_Reduction(EXT, GroupExt, ThePath, "CDD");
end;

__DualDescriptionPPL_Reduction:=function(EXT, GroupExt, ThePath)
  return __DualDescriptionDoubleDescMethod_Reduction(EXT, GroupExt, ThePath, "PPL");
end;



DualDescriptionCDD:=function(EXT, GroupExt)
  local ThePath;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  return __DualDescriptionCDD_Reduction(EXT, GroupExt, ThePath);
end;


DualDescriptionPPL:=function(EXT, GroupExt)
  local ThePath;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  return __DualDescriptionPPL_Reduction(EXT, GroupExt, ThePath);
end;


# Here we implement the enumeration by using the PD
# method equivariantly.
# That is, once we find a new facet, we add it systematically.
__DualDescriptionPD_Reduction:=function(EXT, GRP, ThePath)
  local EXTpoly, TheDim, nbVert, ListOrbit, FAC, FuncInsert, FuncInsertIfNew, nb, ListSets, eSet, EXTfind, EXTfindCan, EXTcall, eFAC, EXTpolySet, GetFACnew, ListWrong, iWrong, jWrong, nbWrong, eEXT, ListStatus, fEXT, FACnew;
  EXTpoly:=PolytopizationGeneralCone(EXT);
  EXTpolySet:=Set(EXTpoly);
  TheDim:=Length(EXTpoly[1]);
  nbVert:=Length(EXTpoly);
  ListOrbit:=[];
  FAC:=[];
  GetFACnew:=function(eOrb)
    local FACnew, O, eRepr, eFAC;
    FACnew:=[];
    O:=Orbit(GRP, eOrb, OnSets);
    for eRepr in O
    do
      eFAC:=__FindFacetInequality(EXTpoly, eRepr);
      Add(FACnew, eFAC);
    od;
    return FACnew;
  end;
  FuncInsert:=function(eOrb)
    Add(ListOrbit, eOrb);
    Append(FAC, GetFACnew(eOrb));
  end;
  FuncInsertIfNew:=function(eOrb)
    local fOrb, test;
    for fOrb in ListOrbit
    do
      test:=RepresentativeAction(GRP, eOrb, fOrb, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    FuncInsert(eOrb);
  end;
  #
  # First part of the enumeration:
  # Finding sufficient inequality for a full dimensional polytope.
  #
  while(true)
  do
    nb:=10;
    ListSets:=GetInitialRaysEXT(EXTpoly, nb);
    for eSet in ListSets
    do
      FuncInsertIfNew(eSet);
    od;
    if RankMat(FAC)=TheDim then
      break;
    fi;
  od;
  #
  # Second part of the enumeration:
  # Iterating with linear programs
  #
  while(true)
  do
    EXTfind:=DualDescription(FAC);
    ListWrong:=[];
    for eEXT in EXTfind
    do
      if eEXT[1] <= 0 then
        Add(ListWrong, eEXT);
      else
        fEXT:=eEXT/eEXT[1];
        if not(fEXT in EXTpolySet) then
          Add(ListWrong, eEXT);
        fi;
      fi;
    od;
    nbWrong:=Length(ListWrong);
    if nbWrong=0 then
      break;
    fi;
    ListStatus:=ListWithIdenticalEntries(nbWrong,0);
    for iWrong in [1..nbWrong]
    do
      if ListStatus[iWrong]=0 then
        eSet:=GetViolatedFacet(EXTpoly, ListWrong[iWrong]);
        Add(ListOrbit, eSet);
        FACnew:=GetFACnew(eSet);
        Append(FAC, FACnew);
        for jWrong in [iWrong..nbWrong]
        do
          if ListStatus[jWrong]=0 then
            if First(FACnew, x->x*ListWrong[jWrong]<0)<>fail then
              ListStatus[jWrong]:=1;
            fi;
          fi;
        od;
      fi;
    od;
  od;
  return ListOrbit;
end;

__DualDescriptionPD_Reduction_Equivariant:=function(EXT, GRP)
  local ThePath;
  ThePath:="/irrelevant";
  return __DualDescriptionPD_Reduction(EXT, GRP, ThePath);
end;

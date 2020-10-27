BindGlobal("POLYHEDRAL_tmpdir",DirectoryTemporary());

FileIsEmptyFile:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"IsEmptyFile");
FileVectorCddGap:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"VectorCddGap");
FileConvertListFileAsVector:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ConvListFile");


RemoveFileIfExist:=function(FileName)
  if IsExistingFile(FileName)=true then
    RemoveFile(FileName);
  fi;
end;

SaveDataToFile:=function(FileName, OBJ)
  local output;
  Exec("rm -f ", FileName,"\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "return ", OBJ, ";\n");
  CloseStream(output);
end;




GetFinalFile:=function(eFile)
  local LStr;
  LStr:=STRING_Split(eFile, "/").ListStrInter;
  return LStr[Length(LStr)];
end;


GetDirectoryFromFile:=function(eFile)
  local len, i, pos;
  len:=Length(eFile);
  pos:=-1;
  for i in [1..len]
  do
    if eFile[i]='/' then
      pos:=i;
    fi;
  od;
  if pos=-1 then
    Error("We did not find the / in the string");
  fi;
  return eFile{[1..pos]};
end;


SaveDataToFilePlusTouch:=function(FileName, OBJ)
  local FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFileIfExist(FileTouch);
  SaveDataToFile(FileName, OBJ);
  SaveDataToFile(FileTouch, 0);
end;

IsExistingFilePlusTouch:=function(FileName)
  local FileTouch;
  if IsExistingFile(FileName)=false then
    return false;
  fi;
  FileTouch:=Concatenation(FileName, "_touch");
  return IsExistingFile(FileTouch);
end;





IsEmptyFile:=function(FileName)
  local FileRep, TheRep;
  FileRep:=Filename(POLYHEDRAL_tmpdir, "FileInterpretation");
  Exec(FileIsEmptyFile, " ", FileName, " > ", FileRep);
  TheRep:=ReadAsFunction(FileRep)();
  RemoveFile(FileRep);
  return TheRep;
end;

ReadVectorFile:=function(FileName)
  local Ftmp, DataVar;
  Ftmp:=Filename(POLYHEDRAL_tmpdir, "GapFile");
  Exec(FileVectorCddGap, " ", FileName, "> ", Ftmp);
  DataVar:=ReadAsFunction(Ftmp)();
  RemoveFile(Ftmp);
  return DataVar;
end;


SaveStringToFile:=function(FileName, eStr)
  local output;
  Exec("rm -f ", FileName,"\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "return \"", eStr, "\";");
  CloseStream(output);
end;

SaveDataToFilePlusGzip:=function(FileName, OBJ)
  local output, FileNameGzip;
  FileNameGzip:=Concatenation(FileName, ".gz");
  Exec("rm -f ", FileName, "\n");
  Exec("rm -f ", FileNameGzip, "\n");
  output:=OutputTextFile(FileName, true);;
  AppendTo(output, "return ", OBJ, ";\n");
  CloseStream(output);
  Exec("gzip ", FileName);
end;


RemoveFilePlusTouch:=function(FileName)
  local FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFile(FileName);
  RemoveFile(FileTouch);
end;




SaveDataToFilePlusTouchPlusTest:=function(FileName, OBJ, test)
  if test=true then
    SaveDataToFilePlusTouch(FileName, OBJ);
  fi;
end;

SaveDataToFilePlusGzipPlusTouch:=function(FileName, OBJ)
  local FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFileIfExist(FileTouch);
  SaveDataToFilePlusGzip(FileName, OBJ);
  SaveDataToFile(Concatenation(FileName, "_touch"), 0);
end;


SaveDataToFilePlusGzipPlusTouchPlusTest:=function(FileName, OBJ, test)
  if test=true then
    SaveDataToFilePlusGzipPlusTouch(FileName, OBJ);
  fi;
end;




ReadAsFunctionPlusGzip:=function(FileName)
  local FilePre, FileD, W, FileGziped;
  FileGziped:=Concatenation(FileName, ".gz");
  FileD:=Filename(POLYHEDRAL_tmpdir,"Uncompressed");
  Exec("gunzip -c ", FileName, " > ", FileD);
  W:=ReadAsFunction(FileD);
  RemoveFile(FileD);
  return W;
end;



ComputeAndSave:=function(FileName, FCT)
  local TheData;
  if IsExistingFile(FileName)=true then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    SaveDataToFile(FileName, TheData);
    return TheData;
  fi;
end;






ComputeAndSaveIfTest:=function(FileName, TheTest, FCT)
  local TheData;
  if TheTest=true and IsExistingFile(FileName)=true then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    if TheTest=true then
      SaveDataToFile(FileName, TheData);
    fi;
    return TheData;
  fi;
end;




RemoveDirectoryPlusTest:=function(FileDirectory, test)
  if test=true then
    Exec("rm -rf ", FileDirectory);
  fi;
end;

CreateDirectory:=function(FileDirectory)
  Exec("mkdir -p ", FileDirectory);
end;

CreateDirectoryPlusTest:=function(FileDirectory, test)
  if test=true then
    Exec("mkdir -p ", FileDirectory);
  fi;
end;



RemoveFileIfExistPlusTouch:=function(FileName)
  local FileTouch;
  RemoveFileIfExist(FileName);
  FileTouch:=Concatenation(FileName, "_touch");
  RemoveFileIfExist(FileTouch);
end;

RemoveFileIfExistPlusTouchPlusTest:=function(FileName, test)
  if test=true then
    RemoveFileIfExistPlusTouch(FileName);
  fi;
end;




IsExistingFilePlusGzipPlusTouchPlusTest:=function(FileName, test)
  local FileTouch, FileGziped;
  if test=false then
    return false;
  else
    FileTouch:=Concatenation(FileName, "_touch");
    FileGziped:=Concatenation(FileName, ".gz");
    return IsExistingFile(FileTouch) and IsExistingFile(FileGziped);
  fi;
end;



IsExistingFilePlusTouchPlusTest:=function(FileName, test)
  local FileTouch;
  if test=false then
    return false;
  else
    FileTouch:=Concatenation(FileName, "_touch");
    if IsExistingFile(FileName)=false then
      return false;
    fi;
    return IsExistingFile(FileTouch);
  fi;
end;



RecollectTest:=function(FileName, test)
  if test=true then
    if IsExistingFile(FileName)=true then
      Error("Forget to run a Recollect function");
    fi;
  fi;
end;



ReadAsFunctionPlusTouchPlusTest:=function(FileName, DefaultVal, test)
  if test=false then
    return DefaultVal;
  else
    if IsExistingFilePlusTouch(FileName)=false then
      SaveDataToFilePlusTouch(FileName, DefaultVal);
      return DefaultVal;
    fi;
    return ReadAsFunction(FileName)();
  fi;
end;



ComputeAndSave:=function(FileName, FCT)
  local TheData, FileTouch;
  FileTouch:=Concatenation(FileName, "_touch");
  if IsExistingFile(FileName)=true then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    SaveDataToFilePlusTouch(FileName, TheData);
    return TheData;
  fi;
end;



ComputeAndSavePlusTouch:=function(FileName, FCT)
  local TheData;
  if IsExistingFilePlusTouch(FileName)=true then
    return ReadAsFunction(FileName)();
  else
    TheData:=FCT(1);
    SaveDataToFilePlusTouch(FileName, TheData);
    return TheData;
  fi;
end;



ComputeAndSavePlusTouchPlusTest:=function(FileName, FCT, test)
  if test=false then
    return FCT(1);
  else
    return ComputeAndSavePlusTouch(FileName, FCT);
  fi;
end;



SaveDataToFileRecoverablePrevState:=function(FileName, Data)
  local File1, File2, File1touch, File2touch;
  File1:=Concatenation(FileName, "_1");
  File2:=Concatenation(FileName, "_2");
  File1touch:=Concatenation(File1, "_touch");
  File2touch:=Concatenation(File2, "_touch");
  SaveDataToFile(File2, Data);
  SaveDataToFile(File2touch, 0);
  RemoveFileIfExist(File1touch);
  RemoveFileIfExist(File1);
  Exec("cp ", File2, " ", File1);
  Exec("cp ", File2touch, " ", File1touch);
end;



SaveDataToFileRecoverablePrevStatePlusTest:=function(FileName, Data, test)
  if test=true then
    SaveDataToFileRecoverablePrevState(FileName, Data);
  fi;
end;



ReadAsFunctionRecoverablePrevState:=function(FileName)
  local File1, File2, File1touch, File2touch;
  File1:=Concatenation(FileName, "_1");
  File2:=Concatenation(FileName, "_2");
  File1touch:=Concatenation(File1, "_touch");
  File2touch:=Concatenation(File2, "_touch");
  if IsExistingFile(File1touch)=true then
    return ReadAsFunction(File1)();
  fi;
  if IsExistingFile(File2touch)=true then
    return ReadAsFunction(File2)();
  fi;
end;



IsExistingFileRecoverablePrevState:=function(FileName)
  local File1, File2, File1touch, File2touch;
  File1:=Concatenation(FileName, "_1");
  File2:=Concatenation(FileName, "_2");
  File1touch:=Concatenation(File1, "_touch");
  File2touch:=Concatenation(File2, "_touch");
  if IsExistingFile(File2touch)=true then
    return true;
  fi;
  if IsExistingFile(File1touch)=true then
    return true;
  fi;
  return false;
end;


# TheComm can be something like
# "ssh r ls TheComputation/LEGO/DATAcase"
LSoperation:=function(TheComm)
  local FileList, TheCommFull, FileFinal, TheListFinal, TheCommand;
  FileList:=Filename(POLYHEDRAL_tmpdir, "ListFile");
  TheCommFull:=Concatenation(TheComm, " > ", FileList);
  Exec(TheCommFull);
  #
  FileFinal:=Filename(POLYHEDRAL_tmpdir, "ListFinal");
  TheCommand:=Concatenation(FileConvertListFileAsVector, " ", FileList, " > ", FileFinal);
  Exec(TheCommand);
  #
  TheListFinal:=ReadAsFunction(FileFinal)();
  RemoveFileIfExist(FileFinal);
  RemoveFileIfExist(FileList);
  return TheListFinal;
end;

# Replace the / by _
FullFileAsString:=function(eFile)
  local LStr, eStr, i;
  LStr:=STRING_Split(eFile, "/").ListStrInter;
  eStr:=LStr[1];
  for i in [2..Length(LStr)]
  do
    eStr:=Concatenation(eStr, "_", LStr[i]);
  od;
  return eStr;
end;

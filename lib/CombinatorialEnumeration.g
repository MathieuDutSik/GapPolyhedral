FileLibexactSolve:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"libexact_solve");
FileLibexactConvertGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"libexact_convertGAP");

#
# find solutions of X A = Y.
# The matrix A must be with entries in 0,1
#
# VectXcond specifies the range of x (if equal 1, var is binary)
# VectYcond specified the range of y 
EnumerateLibexactSolution:=function(TheMat, VectXcond, VectYcond)
  local nbRow, nbCol, FileIN, FileOUT, FileRES, output, iCol, iRow, TheCommand, ListSol, eVal;
  nbRow:=Length(TheMat);
  nbCol:=Length(TheMat[1]);
  FileIN:=Filename(POLYHEDRAL_tmpdir,"Libexact.in");
  FileOUT:=Filename(POLYHEDRAL_tmpdir,"Libexact.out");
  FileRES:=Filename(POLYHEDRAL_tmpdir,"Libexact.res");
  RemoveFileIfExist(FileIN);
  RemoveFileIfExist(FileOUT);
  RemoveFileIfExist(FileRES);
  output:=OutputTextFile(FileIN, true);
  for iCol in [1..nbCol]
  do
    eVal:=VectYcond[iCol];
    if eVal=1 then
      AppendTo(output, "r ", iCol, "\n");
    else
      AppendTo(output, "r ", iCol, " ", eVal, "\n");
    fi;
  od;
  for iRow in [1..nbRow]
  do
    eVal:=VectXcond[iRow];
    if eVal=1 then
      AppendTo(output, "c ", iRow, "\n");
    else
      AppendTo(output, "c ", iRow, " ", eVal, "\n");
    fi;
  od;
  for iRow in [1..nbRow]
  do
    for iCol in [1..nbCol]
    do
      eVal:=TheMat[iRow][iCol];
      if eVal<>0 and eVal<>1 then
        Error("The matrix should have 0,1 entries for libexact");
      fi;
      if eVal=1 then
        AppendTo(output, "e ", iCol, " ", iRow, "\n");
      fi;
    od;
  od;
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileLibexactSolve, " ", FileIN, " > ", FileOUT);
  Exec(TheCommand);
  #
  TheCommand:=Concatenation(FileLibexactConvertGAP, " ", FileOUT, " ", FileRES);
  Exec(TheCommand);
  #
  ListSol:=ReadAsFunction(FileRES)();
  RemoveFileIfExist(FileIN);
  RemoveFileIfExist(FileOUT);
  RemoveFileIfExist(FileRES);
  return ListSol;
end;










Generic_EnumerationSubsets:=function(nbVect, PermGRP, KillingFunction, TheRec)
  local ListSolution, ListMaximal, NewListSolution, FuncInsert, eSol, TheStab, TheDiff, O, eO, eSet, IsMaximal, TotalListSolution, ordGRP, ListNbSol, TotalNbSol, eMax, eVal, TheSize;
  ordGRP:=Order(PermGRP);
  ListSolution:=[ [] ];
  ListMaximal:=[];
  TotalListSolution:=[];
  ListNbSol:=[];
  TheSize:=0;
  while(true)
  do
    if TheRec.AllSolution then
      Add(TotalListSolution, ListSolution);
    fi;
    NewListSolution:=[];
    FuncInsert:=function(NewSol)
      local eSol, TheMinSol;
      if TheRec.MinimumStrategy then
        TheMinSol:=Minimum(Orbit(PermGRP, NewSol, OnSets));
        if TheMinSol<NewSol then
          return;
        fi;
      else
        for eSol in NewListSolution
        do
          if RepresentativeAction(PermGRP, eSol, NewSol, OnSets)<>fail then
            return;
          fi;
        od;
      fi;
      Add(NewListSolution, NewSol);
    end;
    TotalNbSol:=0;
    for eSol in ListSolution
    do
      if TheRec.MinimumStrategy then
        if TheRec.TotalNbSol then
          TheStab:=Stabilizer(PermGRP, eSol, OnSets);
          TotalNbSol:=TotalNbSol + ordGRP/Order(TheStab);
        fi;
        if Length(eSol)=0 then
          eMax:=0;
        else
          eMax:=Maximum(eSol);
        fi;
        for eVal in [eMax+1..nbVect]
        do
          eSet:=Union(eSol, [eVal]);
          if KillingFunction(eSet)=false then
            FuncInsert(eSet);
          fi;
        od;
        if TheRec.AllMaximal then
          Error("No maximal possible with that strategy");
        fi;
      else
        TheStab:=Stabilizer(PermGRP, eSol, OnSets);
        if TheRec.TotalNbSol then
          TotalNbSol:=TotalNbSol + ordGRP/Order(TheStab);
        fi;
        TheDiff:=Difference([1..nbVect], eSol);
        O:=Orbits(TheStab, TheDiff, OnPoints);
        IsMaximal:=true;
        for eO in O
        do
          eSet:=Union(eSol, [eO[1]]);
          if KillingFunction(eSet)=false then
            IsMaximal:=false;
            FuncInsert(eSet);
          fi;
        od;
        if IsMaximal=true and TheRec.AllMaximal then
          Add(ListMaximal, eSol);
        fi;
      fi;
    od;
    Add(ListNbSol, TotalNbSol);
    ListSolution:=ShallowCopy(NewListSolution);
    Print("|ListSolution|=", Length(ListSolution), "\n");
    if Length(ListSolution)=0 then
      break;
    fi;
    if TheRec.MaximumSize<>-1 then
      if TheSize=TheRec.MaximumSize then
        break;
      fi;
    fi;
    TheSize:=TheSize+1;
  od;
  return rec(ListMaximal:=ListMaximal, TotalListSolution:=TotalListSolution, ListNbSol:=ListNbSol);
end;






MyEnumerationMaximal:=function(nbVect, PermGRP, KillingFunction)
  local TheRec;
  TheRec:=rec(AllMaximal:=true,
              TotalNbSol:=false,
              MinimumStrategy:=false,
	      MaximumSize:=-1,
              AllSolution:=false);
  return Generic_EnumerationSubsets(nbVect, PermGRP, KillingFunction, TheRec).ListMaximal;
end;





MyEnumerationMaximalMinimalSpanning:=function(IsSaving, ThePrefix, nbVect, PermGRP, SpanningFunction)
  local ListSolution, ListMaximalSurviving, NewListSolution, eSol, TheStab, TheDiff, O, eO, eSet, ListOrbitMinimallyKilled, ListMinimallyKilled, IsMaximal, idx, IsKilledByBook, FuncInsertListMinimallyKilled, ListTested, IsPresentKill, IsPresentKept, FileSave, testKillBook, ListKilled, testListKept, testListKill, Ocorrect, Oincorrect, TheSpann;
  ListSolution:=[ [] ];
  ListMaximalSurviving:=[];
  ListOrbitMinimallyKilled:=[];
  ListMinimallyKilled:=[];
  IsKilledByBook:=function(eSet)
    local vSet;
    for vSet in ListMinimallyKilled
    do
      if IsSubset(eSet, vSet)=true then
        return true;
      fi;
    od;
    return false;
  end;
  FuncInsertListMinimallyKilled:=function(eSet)
    local fSet;
    for fSet in ListOrbitMinimallyKilled
    do
      if RepresentativeAction(PermGRP, eSet, fSet, OnSets)<>fail then
        return;
      fi;
    od;
    Add(ListOrbitMinimallyKilled, eSet);
    FileSave:=Concatenation(ThePrefix, "ListMinimallyKilled");
    if IsSaving=true then
      SaveDataToFile(FileSave, ListOrbitMinimallyKilled);
    fi;
    Append(ListMinimallyKilled, Orbit(PermGRP, eSet, OnSets));
  end;
  idx:=0;
  while(true)
  do
    idx:=idx+1;
    NewListSolution:=[];
    IsPresentKept:=function(NewSol)
      local eSol;
      for eSol in NewListSolution
      do
        if RepresentativeAction(PermGRP, eSol, NewSol, OnSets)<>fail then
          return true;
        fi;
      od;
      return false;
    end;
    for eSol in ListSolution
    do
      TheSpann:=SpanningFunction(eSol);
      TheStab:=Stabilizer(PermGRP, eSol, OnSets);
      if Length(TheSpann.ListCorrect)=0 then
        IsMaximal:=true;
      else
        IsMaximal:=false;
      fi;
      Ocorrect:=Orbits(TheStab, TheSpann.ListCorrect, OnPoints);
      Oincorrect:=Orbits(TheStab, TheSpann.ListIncorrect, OnPoints);
      for eO in Ocorrect
      do
        eSet:=Union(eSol, [eO[1]]);
        testListKept:=IsPresentKept(eSet);
        if testListKept=false then
          Add(NewListSolution, eSet);
        fi;
      od;
      for eO in Oincorrect
      do
        eSet:=Union(eSol, [eO[1]]);
        testKillBook:=IsKilledByBook(eSet);
        if testKillBook=false then
          FuncInsertListMinimallyKilled(eSet);
        fi;
      od;
      if IsMaximal=true then
        Add(ListMaximalSurviving, eSol);
        FileSave:=Concatenation(ThePrefix, "ListMaximalSurviving");
        if IsSaving=true then
          SaveDataToFile(FileSave, ListMaximalSurviving);
        fi;
      fi;
    od;
    ListSolution:=ShallowCopy(NewListSolution);
    FileSave:=Concatenation(ThePrefix, "ListSolution", String(idx));
    if IsSaving=true then
      SaveDataToFile(FileSave, ListSolution);
    fi;
    Print("idx=", idx, "  |ListMaximalSurviving|=", Length(ListMaximalSurviving), "  |ListSolution|=", Length(ListSolution), "\n");
    if Length(ListSolution)=0 then
      break;
    fi;
  od;
  return rec(ListMaximalSurviving:=ListMaximalSurviving, 
             ListOrbitMinimallyKilled:=ListOrbitMinimallyKilled);
end;





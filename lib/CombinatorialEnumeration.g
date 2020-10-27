FileEnumKset:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"COMB_EnumerationKset");
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









Enumerate_Ksets:=function(nbVect, PermGRP, k)
  local FileGRP, FileOUT, output, eElt, iVect, iVectImg, TheCommand, ListKset;
  FileGRP:=Filename(POLYHEDRAL_tmpdir,"GroupDesc.ext");
  FileOUT:=Filename(POLYHEDRAL_tmpdir,"ListKset.gap");
  output:=OutputTextFile(FileGRP, true);
  AppendTo(output, nbVect, "\n");
  AppendTo(output, Order(PermGRP), "\n");
  for eElt in PermGRP
  do
    for iVect in [1..nbVect]
    do
      iVectImg:=OnPoints(iVect, eElt);
      AppendTo(output, " ", iVectImg-1);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileEnumKset, " ", FileGRP, " ", String(k), " ", FileOUT);
  Exec(TheCommand);
  #
  ListKset:=ReadAsFunction(FileOUT)();
  RemoveFileIfExist(FileOUT);
  RemoveFileIfExist(FileGRP);
  return ListKset;
end;

Generic_EnumerationSubsets_Extended:=function(nbVect, PermGRP, KillingFunction, SpanningFunction, FeasiblingFunction, InvariantingFunction, TheRec)
  local ListSolution, ListMaximal, NewListSolution, FuncInsert, eSol, TheStab, TheDiff, O, eO, eSet, IsMaximal, TotalListSolution, ordGRP, TotalNbSol, eMax, eVal, TheSize, ListInv;
  ordGRP:=Order(PermGRP);
  ListSolution:=[ [] ];
  ListMaximal:=[];
  TotalListSolution:=[];
  TheSize:=1;
  while(true)
  do
    NewListSolution:=[];
    ListInv:=[];
    FuncInsert:=function(NewSol)
      local len, i, eSol, NewInv;
      len:=Length(NewListSolution);
      NewInv:=InvariantingFunction(NewSol);
      for i in [1..len]
      do
#        if ListInv[i]=NewInv then
          if RepresentativeAction(PermGRP, NewSol, NewListSolution[i], OnSets)<>fail then
            return;
          fi;
#        fi;
      od;
      Add(NewListSolution, NewSol);
      Add(ListInv, NewInv);
    end;
    for eSol in ListSolution
    do
      TheStab:=Stabilizer(PermGRP, eSol, OnSets);
      TheDiff:=FeasiblingFunction(eSol);
      O:=Orbits(TheStab, TheDiff, OnPoints);
      IsMaximal:=true;
      for eO in O
      do
        eSet:=SpanningFunction(Union(eSol, [eO[1]]));
        if KillingFunction(eSet)=false then
          IsMaximal:=false;
          FuncInsert(eSet);
        fi;
      od;
      if IsMaximal=true and TheRec.AllMaximal then
        Add(ListMaximal, eSol);
      fi;
    od;
    ListSolution:=ShallowCopy(NewListSolution);
    Print("|ListSolution|=", Length(ListSolution), " TheSize=", TheSize, "\n");
    if TheRec.AllSolution then
      Add(TotalListSolution, ListSolution);
    fi;
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
  return rec(ListMaximal:=ListMaximal, TotalListSolution:=TotalListSolution);
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


# This function determines the list of maximal element and
# minimally killed.
# it works under the assumption that testing kill is expensive.
MyEnumerationMaximalMinimal:=function(IsSaving, ThePrefix, nbVect, PermGRP, KillingFunction, KeepInKillBank)
  local ListSolution, ListMaximalSurviving, NewListSolution, eSol, TheStab, TheDiff, O, eO, eSet, ListOrbitMinimallyKilled, ListMinimallyKilled, IsMaximal, idx, IsKilledByBook, FuncInsertListKilled, ListTested, IsPresentKill, IsPresentKept, FileSave, testKillBook, ListKilled, testListKept, testListKill;
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
  FuncInsertListKilled:=function(eSet)
    if KeepInKillBank(eSet)=true then
      Add(ListOrbitMinimallyKilled, eSet);
      FileSave:=Concatenation(ThePrefix, "ListMinimallyKilled");
      if IsSaving=true then
        SaveDataToFile(FileSave, ListOrbitMinimallyKilled);
      fi;
      Append(ListMinimallyKilled, Orbit(PermGRP, eSet, OnSets));
    fi;
  end;
  ListSolution:=[ [] ];
  idx:=0;
  while(true)
  do
    idx:=idx+1;
    NewListSolution:=[];
    ListKilled:=[];
    IsPresentKill:=function(NewSol)
      local eSol;
      for eSol in ListKilled
      do
        if RepresentativeAction(PermGRP, eSol, NewSol, OnSets)<>fail then
          return true;
        fi;
      od;
      return false;
    end;
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
      TheStab:=Stabilizer(PermGRP, eSol, OnSets);
      TheDiff:=Difference([1..nbVect], eSol);
      O:=Orbits(TheStab, TheDiff, OnPoints);
      IsMaximal:=true;
      for eO in O
      do
        eSet:=Union(eSol, [eO[1]]);
        testListKill:=IsPresentKill(eSet);
        testListKept:=IsPresentKept(eSet);
        if testListKept=true then
          IsMaximal:=false;
        fi;
        if testListKill=false and testListKept=false then
          testKillBook:=IsKilledByBook(eSet);
          if testKillBook=true then
            Add(ListKilled, eSet);
          fi;
          if testKillBook=false then
            if KillingFunction(eSet)=true then
              Add(ListKilled, eSet);
              FuncInsertListKilled(eSet);
            else
              IsMaximal:=false;
              Add(NewListSolution, eSet);
            fi;
          fi;
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



MyFindOrbitSubGraphsNautyMethod:=function(nbv, TheGRA, FuncSelect, AskedSize)
  local GRP, ListAdjacency, O, Cand, eOrb, iP, CandSec, Stab, O2, eO2, eCand, FuncInsert;
  #
  GRP:=AutGroupGraph(TheGRA);
  ListAdjacency:=__GetListAdjacency(TheGRA);
  O:=Orbits(GRP, [1..nbv], OnPoints);
  Cand:=[];
  for eOrb in O
  do
    AddSet(Cand, [Minimum(eOrb)]);
  od;
#  Print("Find ",Length(O)," orbits at step 1\n");
  #
  for iP in [2..AskedSize]
  do
    CandSec:=[];
    for eCand in Cand
    do
      Stab:=Stabilizer(GRP, eCand, OnSets);
      O2:=Orbits(Stab, Difference([1..nbv], eCand), OnPoints);
      for eO2 in O2
      do
        AddSet(CandSec, Union(eCand, [eO2[1]]));
      od;
    od;
    Cand:=[];
    for eCand in CandSec
    do
      if FuncSelect(eCand)=true then
        AddSet(Cand, eCand);
      fi;
    od;
    CandSec:=[];
    FuncInsert:=function(eCand)
      local fCand, TheCanon;
      TheCanon:=CharacteristicGraphOfSubsetAdjList(ListAdjacency, eCand);
      for fCand in CandSec
      do
        if fCand.TheCanon=TheCanon then
          return;
        fi;
      od;
      Add(CandSec, rec(eCand:=eCand, TheCanon:=TheCanon));
    end;
    for eCand in Cand
    do
      FuncInsert(eCand);
    od;
    Cand:=List(CandSec, x->x.eCand);
#    Print("Find ", Length(Cand)," orbits at step ", iP, "\n");
  od;
  return Cand;
end;


COMBENUM_GetInitialCandidates:=function(nbv, TheGroup, FuncSelect)
  local O, ListCand, eOrb, eCand;
  O:=Orbits(TheGroup, [1..nbv], OnPoints);
  ListCand:=[];
  for eOrb in O
  do
    eCand:=[Minimum(eOrb)];
    if FuncSelect(eCand)=true then
      Add(ListCand, eCand);
    fi;
  od;
  return ListCand;
end;


COMBENUM_KernelSingleIncrement:=function(nbv, TheGroup, TestEquivalence, GetStabilizer, FuncSelect, FuncInvariant, PrevListCand)
  local ListCand, FuncInsert, eStab, O2, eO2, eCand, eNewCand, eMin, MaxValEcand, ListInvariant, iCand, len;
  ListCand:=[];
  ListInvariant:=[];
  FuncInsert:=function(eCand)
    local iCand, fCand, eInv;
    eInv:=FuncInvariant(eCand);
    for iCand in [1..Length(ListCand)]
    do
      if ListInvariant[iCand]=eInv then
        fCand:=ListCand[iCand];
#        Print("Testing for eCand=", eCand, " fCand=", fCand, "\n");
        if TestEquivalence(eCand, fCand)<>fail then
          return;
        fi;
      fi;
    od;
    Add(ListCand, eCand);
    Add(ListInvariant, eInv);
  end;
  len:=Length(PrevListCand);
  for iCand in [1..len]
  do
    eCand:=PrevListCand[iCand];
    eStab:=GetStabilizer(eCand);
    MaxValEcand:=Maximum(eCand);
    O2:=Orbits(eStab, Difference([1..nbv], eCand), OnPoints);
#    Print("iCand=", iCand, "/", len, " |eStab|=", Order(eStab), " |O2|=", Length(O2), "\n");
    for eO2 in O2
    do
      eMin:=Minimum(eO2);
      if eMin>MaxValEcand then
        eNewCand:=Concatenation(eCand, [eMin]);
        if FuncSelect(eNewCand)=true then
          FuncInsert(eNewCand);
        fi;
      fi;
    od;
  od;
  return ListCand;
end;



COMBENUM_KernelSingleIncrementCanonic:=function(nbv, TheGroup, TestEquivalence, GetStabilizer, FuncSelect, FuncCanonic, PrevListCand)
  local ListCand, FuncInsert, eStab, O2, eO2, eCand, eNewCand, eMin, MaxValEcand, ListCanonic, iCand, len;
  ListCand:=[];
  ListCanonic:=[];
  FuncInsert:=function(eCand)
    local iCand, fCand, eCan;
    eCan:=FuncCanonic(eCand);
    if Position(ListCanonic, eCan)<>fail then
      return;
    fi;
    Add(ListCand, eCand);
    AddSet(ListCanonic, eCan);
  end;
  len:=Length(PrevListCand);
  for iCand in [1..len]
  do
    eCand:=PrevListCand[iCand];
    eStab:=GetStabilizer(eCand);
    MaxValEcand:=Maximum(eCand);
    O2:=Orbits(eStab, Difference([1..nbv], eCand), OnPoints);
#    Print("iCand=", iCand, "/", len, " |eStab|=", Order(eStab), " |O2|=", Length(O2), "\n");
    for eO2 in O2
    do
      eMin:=Minimum(eO2);
      if eMin>MaxValEcand then
        eNewCand:=Concatenation(eCand, [eMin]);
        if FuncSelect(eNewCand)=true then
          FuncInsert(eNewCand);
        fi;
      fi;
    od;
  od;
  return ListCand;
end;




KernelFindOrbitSubGraphs:=function(nbv, TheGroup, TestEquivalence, GetStabilizer, FuncSelect, FuncInvariant, AskedSize)
  local O, ListListCand, ListCand, eOrb, iP, eStab, O2, eO2, eCand, eNewCand, FuncInsert;
  #
  ListListCand:=[];
  ListCand:=COMBENUM_GetInitialCandidates(nbv, TheGroup, FuncSelect);
  Add(ListListCand, ListCand);
#  Print("Find ", Length(ListCand), " orbits at step 1\n");
  #
  for iP in [2..AskedSize]
  do
    ListCand:=COMBENUM_KernelSingleIncrement(nbv, TheGroup, TestEquivalence, GetStabilizer, FuncSelect, FuncInvariant, ListListCand[iP-1]);
    Add(ListListCand, ListCand);
#    Print("Find ", Length(ListCand), " orbits at step ", iP, "\n");
  od;
  return ListListCand;
end;

MyFindOrbitSubGraphs:=function(nbv, TheGroup, FuncSelect, AskedSize)
  local TestEquivalence, GetStabilizer, FuncInvariant;
  TestEquivalence:=function(eCand, fCand)
    return RepresentativeAction(TheGroup, eCand, fCand, OnSets);
  end;
  GetStabilizer:=function(eCand)
    return Stabilizer(TheGroup, eCand, OnSets);
  end;
  FuncInvariant:=function(eCand)
    return 0;
  end;
  return KernelFindOrbitSubGraphs(nbv, TheGroup, TestEquivalence, GetStabilizer, FuncSelect, FuncInvariant, AskedSize);
end;





GetOrbitsIndependentFixedRank:=function(ListVect, PermGRP, TheRnk)
  local KillingFunction, ListOrbits;
  KillingFunction:=function(eSet)
    if Length(eSet) > TheRnk then
      return true;
    fi;
    if RankMat(ListVect{eSet})=Length(eSet) then
      return false;
    else
      return true;
    fi;
  end;
  ListOrbits:=MyEnumerationMaximal(Length(ListVect), PermGRP, KillingFunction);
  return Filtered(ListOrbits, x->Length(x)=TheRnk);
end;


EnumerationPossibleVectors:=function(n, k)
  local IdMat, ListPoss, iter, NewListPoss, i, eVect, fVect;
  IdMat:=IdentityMat(n);
  ListPoss:=[ListWithIdenticalEntries(n, 0)];
  for iter in [1..k]
  do
    NewListPoss:=[];
    for eVect in ListPoss
    do
      for i in [1..n]
      do
        fVect:=eVect + IdMat[i];
        Add(NewListPoss, fVect);
      od;
    od;
    ListPoss:=Set(NewListPoss);
  od;
  return ListPoss;
end;

GetKset_fromLowerSet:=function(GRP, ListOrb, n)
  local nLow, ListPoss, NewListOrb, eOrb, eStab, eStabRed, Oposs, eOposs, eVect, nOrb, i, j, eMult, ePt;
  nLow:=Length(ListOrb[1]);
  ListPoss:=EnumerationPossibleVectors(nLow, n - nLow);
  NewListOrb:=[];
  for eOrb in ListOrb
  do
    eStab:=Stabilizer(GRP, eOrb, OnSets);
    eStabRed:=SecondReduceGroupAction(eStab, eOrb);
    Oposs:=Orbits(eStabRed, ListPoss, Permuted);
    for eOposs in Oposs
    do
      eVect:=eOposs[1] + ListWithIdenticalEntries(nLow,1);
      nOrb:=[];
      for i in [1..nLow]
      do
        eMult:=eVect[i];
        ePt:=eOrb[i];
        for j in [1..eMult]
        do
          Add(nOrb, ePt);
        od;
      od;
      Add(NewListOrb, nOrb);
    od;
  od;
  return NewListOrb;
end;



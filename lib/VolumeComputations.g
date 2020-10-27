TestCorrectness:=function(EXT, eSetW, TheSelectW)
  local EXTred;
  EXTred:=List(EXT{eSetW}, x->x{TheSelectW});
  if RankMat(EXTred)<>Length(EXTred[1]) then
    Print("The volume of a non full-dimensional polytope is not defined\n");
    Error("Please use ColumnReduction for having correct input\n");
  fi;
end;




PolytopeVolumeRecursive:=function(EXT, GroupEXT)
  local ListFirstColumn, TheSymbol, FuncRespawn, ListCases, FuncCheckInBank, __RecursiveEvaluation, TheRes;
  ListFirstColumn:=List(EXT, x->x[1]);
  if Set(ListFirstColumn)<>[1] then
    Error("First coordinate should always be 1");
  fi;
  if RankMat(EXT)<>Length(EXT[1]) then
    Error("The polytope should be full dimensional");
  fi;
  FuncRespawn:=function(OrdGrp, NBV, TheLevel)
    if NBV < 20 then
      return false;
    fi;
    if NBV > 130 then
      return true;
    fi;
    if OrdGrp > 100 and NBV > 40 then
      return true;
    fi;
    if NBV>100 and OrdGrp>1000 then
      return true;
    fi;
    if TheLevel=2 then
      return false;
    fi;
    if NBV < 70 then
      return false;
    fi;
    if NBV > 110 and OrdGrp > 100 and TheLevel < 2 then
      return true;
    fi;
    return false;
  end;
  ListCases:=[];
  FuncCheckInBank:=function(TheSet, TheSelect)
    local eCase, test, TheMat, ListOrbitRed, ListOrbitImage, ListNewOrbit, eInc, eImg, EXT1red, EXT2, EXT2red, TheNewVolume, EXTred;
    for eCase in ListCases
    do
      test:=RepresentativeAction(GroupEXT, eCase.eSet, TheSet, OnSets);
      if test<>fail then
        TheMat:=FindTransformation(EXT, EXT, test);
        ListOrbitRed:=List(eCase.ListOrbitFacet, x->eCase.eSet{x});
        ListOrbitImage:=List(ListOrbitRed, x->OnSets(x, test));
        ListNewOrbit:=[];
        for eInc in ListOrbitImage
        do
          eImg:=List(eInc, x->Position(TheSet, x));
          Add(ListNewOrbit, Set(eImg));
        od;
        EXT1red:=List(EXT{eCase.eSet}, x->x{eCase.eSelect});
        EXT2:=List(eCase.eSet, x->EXT[OnPoints(x, test)]);
        EXT2red:=List(EXT2, x->x{TheSelect});
        TheMat:=FindTransformation(EXT1red, EXT2red, ());
        TheNewVolume:=eCase.TheVolume*AbsInt(DeterminantMat(TheMat));
        return rec(TheVolume:=TheNewVolume, ListOrbitFacet:=ListNewOrbit);
      fi;
    od;
    return fail;
  end;
  __RecursiveEvaluation:=function(TheSymbol)
    local eSet, TheSelect, TheStab, testRespawn, TheStabRed, TheVolume, FuncInsert, TheRead, EXTred, ListOrbitFacetRed, IsFinished, eVect, TheEval, len, TheSelect2, eSetOrbit, eInc, TheSymbolFacet, eSetMap, RPLift, iOrbit, ListOrbit, nbOrbit, TheMat, eCenter, EXT2, eCenterRed, EXT1, EXTred2, testCheck, TheRecord, StabFacet, OrbSize, TheVol, NewSelect;
    eSet:=TheSymbol.eSet;
    TheSelect:=TheSymbol.TheSelect;
    EXTred:=List(EXT{eSet}, x->x{TheSelect});
    testCheck:=FuncCheckInBank(eSet, TheSelect);
    if testCheck<>fail then
      return testCheck;
    fi;
    TheStab:=Stabilizer(GroupEXT, eSet, OnSets);
    TheStabRed:=SecondReduceGroupAction(TheStab, eSet);
#    Print("|eSet|=", Length(eSet), " rnk=", RankMat(EXTred), " |Stab|=", Order(TheStabRed), "\n");
    testRespawn:=FuncRespawn(Size(TheStabRed), Length(eSet), TheSymbol.TheLevel);
    if testRespawn=true then
      eCenter:=Isobarycenter(EXT{eSet});
      TheVolume:=0;
      ListOrbit:=[];
      FuncInsert:=function(eSubSet)
        local eOrbit, test;
        for eOrbit in ListOrbit
        do
          test:=RepresentativeAction(TheStabRed, eOrbit.eSet, eSubSet, OnSets);
          if test<>fail then
            return;
          fi;
        od;
        Add(ListOrbit, rec(Status:="NO", eSet:=eSubSet));
        Print("|ListOrbit|=", Length(ListOrbit), "\n");
      end;
      eCenterRed:=eCenter{TheSelect};
      for eInc in GetInitialRays_LinProg(EXTred, 10)
      do
        FuncInsert(eInc);
      od;
      while(true)
      do
        nbOrbit:=Length(ListOrbit);
        IsFinished:=true;
        for iOrbit in [1..nbOrbit]
        do
          if ListOrbit[iOrbit].Status="NO" then
            IsFinished:=false;
            ListOrbit[iOrbit].Status:="YES";
            eSetOrbit:=ListOrbit[iOrbit].eSet;
            RPLift:=__ProjectionLiftingFramework(EXTred, eSetOrbit);
            eSetMap:=eSet{eSetOrbit};
            TheSelect2:=ColumnReduction(EXTred{eSetOrbit}).Select;
            NewSelect:=TheSelect{TheSelect2};
            TheSymbolFacet:=rec(TheLevel:=TheSymbol.TheLevel+1, eSet:=eSetMap, TheSelect:=NewSelect);
            TestCorrectness(EXT, eSetMap, NewSelect);
            TheEval:=__RecursiveEvaluation(TheSymbolFacet);
            for eInc in TheEval.ListOrbitFacet
            do
              FuncInsert(RPLift.FuncLift(eInc));
            od;
            EXT1:=Concatenation(EXTred{eSetOrbit}, [eCenterRed]);
            EXTred2:=List(EXTred{eSetOrbit}, x->Concatenation(x{TheSelect2}, [0]));
            len:=Length(EXTred2[1]);
            eVect:=ListWithIdenticalEntries(len,0);
            eVect[len]:=1;
            EXT2:=Concatenation(EXTred2, [eVect]);
            TheMat:=FindTransformation(EXT2, EXT1, ());
            StabFacet:=Stabilizer(TheStabRed, eSetOrbit, OnSets);
            OrbSize:=Order(TheStabRed)/Order(StabFacet);
            TheVol:=TheEval.TheVolume*AbsInt(DeterminantMat(TheMat))/(len-1);
            TheVolume:=TheVolume+OrbSize*TheVol;
          fi;
        od;
        if IsFinished=true then
          break;
        fi;
      od;
      ListOrbitFacetRed:=List(ListOrbit, x->x.eSet);
      TheRead:=rec(ListOrbitFacet:=ListOrbitFacetRed, TheVolume:=TheVolume);
    else
      TheRead:=GetFacetAndVolumePolytope_Reduction(EXTred, TheStabRed);
      if Position(List(TheRead.ListOrbitFacet, Length), Length(EXTred))<>fail then
        Error("Program error in volume computation");
      fi;
    fi;
    TheRecord:=rec(eSet:=eSet, eSelect:=TheSelect, ListOrbitFacet:=TheRead.ListOrbitFacet, TheVolume:=TheRead.TheVolume);
    Add(ListCases, TheRecord);
    return TheRead;
  end;
  TheSymbol:=rec(eSet:=[1..Length(EXT)], TheLevel:=0, TheSelect:=[1..Length(EXT[1])]);
  TheRes:=__RecursiveEvaluation(TheSymbol);
  return TheRes.TheVolume;
end;


VolumeComputationPolytope:=function(EXT)
  local GRP;
  if Length(Set(EXT))<>Length(EXT) then
    Error("Polytope has duplication of its verte set. See you in paradise");
  fi;
  GRP:=LinPolytope_Automorphism(EXT);
  return PolytopeVolumeRecursive(EXT, GRP);
end;

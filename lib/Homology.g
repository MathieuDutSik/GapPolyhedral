

ConvertPolyhedralTesselationToVertexBased:=function(eRecordTessel, ListVectorZeroDimensional, RecOption)
  local len, NewListOrbitByRank, nbOrbit, NewList, iOrbit, eRec, fRec, i, EXT, EXTimage, jOrbit, eBound, eElt, lenBound, iBound, iP, rnk, FAC, eSet, ListPermGens, eGen, eList, TheStabPerm, outputString, eStr, DoStr;
  len:=Length(eRecordTessel.ListOrbitByRank);
  NewListOrbitByRank:=[eRecordTessel.ListOrbitByRank[1]];
  nbOrbit:=Length(eRecordTessel.ListOrbitByRank[2]);
  NewList:=[];
  DoStr:=function()
    Print(eStr);
    outputString:=Concatenation(outputString, eStr);
  end;
  outputString:="";
  eStr:=Concatenation("iRank=0 nbOrbit=", String(nbOrbit), "\n");
  DoStr();
  for iOrbit in [1..nbOrbit]
  do
    eRec:=eRecordTessel.ListOrbitByRank[2][iOrbit];
    eStr:=Concatenation("  iO=", String(iOrbit), " |EXT|=1 |stab|=", String(Order(eRec.TheStab)), "\n");
    DoStr();
    fRec:=rec(EXT:=[ListVectorZeroDimensional[iOrbit]],
              BoundaryImage:=eRec.BoundaryImage);
    if RecOption.DoStab then
      fRec.TheStab:=eRec.TheStab;
      fRec.TheStabPerm:=Group(());
    fi;
    if IsBound(eRec.RotationSubgroup) then
      fRec.RotationSubgroup:=eRec.RotationSubgroup;
    fi;
    Add(NewList, fRec);
  od;
  Add(NewListOrbitByRank, NewList);
  for iP in [3..len]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iP]);
    eStr:=Concatenation("iRank=", String(iP-2), " nbOrbit=", String(nbOrbit), "\n");
    DoStr();
    NewList:=[];
    for iOrbit in [1..nbOrbit]
    do
      eRec:=eRecordTessel.ListOrbitByRank[iP][iOrbit];
      EXT:=[];
      eBound:=eRec.BoundaryImage;
      lenBound:=Length(eBound.ListIFace);
      for iBound in [1..lenBound]
      do
        jOrbit:=eBound.ListIFace[iBound];
        eElt:=eBound.ListElt[iBound];
        EXTimage:=NewListOrbitByRank[iP-1][jOrbit].EXT*eElt;
        EXT:=Union(EXT, Set(EXTimage));
      od;
      if RecOption.DoFAC then
        FAC:=[];
        for iBound in [1..lenBound]
        do
          jOrbit:=eBound.ListIFace[iBound];
          eElt:=eBound.ListElt[iBound];
          EXTimage:=NewListOrbitByRank[iP-1][jOrbit].EXT*eElt;
          eSet:=Set(List(EXTimage, x->Position(EXT, x)));
          Add(FAC, eSet);
        od;
      fi;
      if RecOption.DoStab then
        ListPermGens:=[];
        for eGen in GeneratorsOfGroup(eRec.TheStab)
        do
          eList:=List(EXT, x->Position(EXT, x*eGen));
          Add(ListPermGens, PermList(eList));
        od;
        TheStabPerm:=PersoGroupPerm(ListPermGens);
      fi;
      rnk:=RankMat(EXT);
      if rnk<>iP-1 then
        Error("The rank is not correct for polyhedral tesselation");
      fi;
      eStr:=Concatenation("  iO=", String(iOrbit), " |EXT|=", String(Length(EXT)), " |stab|=", String(Order(eRec.TheStab)), " |bound|=", String(Length(eRec.BoundaryImage.ListIFace)), "\n");
      DoStr();
      fRec:=rec(EXT:=EXT, 
                BoundaryImage:=eRec.BoundaryImage);
      if RecOption.DoFAC then
        fRec.FAC:=FAC;
      fi;
      if RecOption.DoStab then
        fRec.TheStab:=eRec.TheStab;
        fRec.TheStabPerm:=TheStabPerm;
      fi;
      if IsBound(eRec.RotationSubgroup) then
        fRec.RotationSubgroup:=eRec.RotationSubgroup;
      fi;
      Add(NewList, fRec);
    od;
    Add(NewListOrbitByRank, NewList);
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank, 
             IdentityElt:=eRecordTessel.IdentityElt, 
             outputString:=outputString);
end;


ConvertPolyhedralTesselationToIsobarycenter:=function(eRecordTessel, ListVectorZeroDimensional)
  local len, NewListOrbitByRank, nbOrbit, NewList, iOrbit, eRec, fRec, i, EXT, EXTimage, jOrbit, eBound, eElt, lenBound, iBound, iP, rnk, FAC, eSet, ListPermGens, eGen, eList, TheStabPerm, outputString, eStr, DoStr, TheDim, eIso, TheSumVect, TheSumNb, eIsoImage;
  len:=Length(eRecordTessel.ListOrbitByRank);
  NewListOrbitByRank:=[eRecordTessel.ListOrbitByRank[1]];
  nbOrbit:=Length(eRecordTessel.ListOrbitByRank[2]);
  NewList:=[];
  TheDim:=Length(ListVectorZeroDimensional[1]);
  DoStr:=function()
    Print(eStr);
    outputString:=Concatenation(outputString, eStr);
  end;
  outputString:="";
  eStr:=Concatenation("iRank=0 nbOrbit=", String(nbOrbit), "\n");
  DoStr();
  for iOrbit in [1..nbOrbit]
  do
    eRec:=eRecordTessel.ListOrbitByRank[2][iOrbit];
    eStr:=Concatenation("  iO=", String(iOrbit), " |EXT|=1 |stab|=", String(Order(eRec.TheStab)), "\n");
    DoStr();
    fRec:=rec(eIso:=ListVectorZeroDimensional[iOrbit],
              BoundaryImage:=eRec.BoundaryImage);
    Add(NewList, fRec);
  od;
  Add(NewListOrbitByRank, NewList);
  for iP in [3..len]
  do
    nbOrbit:=Length(eRecordTessel.ListOrbitByRank[iP]);
    eStr:=Concatenation("iRank=", String(iP-2), " nbOrbit=", String(nbOrbit), "\n");
    DoStr();
    NewList:=[];
    for iOrbit in [1..nbOrbit]
    do
      eRec:=eRecordTessel.ListOrbitByRank[iP][iOrbit];
      TheSumVect:=[];
      TheSumNb:=0;
      eBound:=eRec.BoundaryImage;
      lenBound:=Length(eBound.ListIFace);
      for iBound in [1..lenBound]
      do
        jOrbit:=eBound.ListIFace[iBound];
        eElt:=eBound.ListElt[iBound];
        eIsoImage:=NewListOrbitByRank[iP-1][jOrbit].eIso*eElt;
        TheSumVect:=TheSumVect+eIsoImage;
        TheSumNb:=TheSumNb+1;
      od;
      eStr:=Concatenation("  iO=", String(iOrbit), " |stab|=", String(Order(eRec.TheStab)), " |bound|=", String(Length(eRec.BoundaryImage.ListIFace)), "\n");
      eIso:=TheSumVect/TheSumNb;
      DoStr();
      fRec:=rec(eIso:=eIso, 
                BoundaryImage:=eRec.BoundaryImage);
      Add(NewList, fRec);
    od;
    Add(NewListOrbitByRank, NewList);
  od;
  return rec(ListOrbitByRank:=NewListOrbitByRank, 
             IdentityElt:=eRecordTessel.IdentityElt, 
             outputString:=outputString);
end;




TranslationGAPresolutionPolyhedralResolution:=function(TheResol, GRP, kLevel)
  local IsInKernel, GetMatrix, DoHomotopy, GetDimension;
  IsInKernel:=function(jRank, TheVector)
    local eVal, TheProd;
    if jRank=0 then
      eVal:=TheVector[1];
      if Sum(eVal.ListVal)<>0 then
        return false;
      else
        return true;
      fi;
    else
      TheProd:=VectorMatrixGmoduleMultiplication(TheVector, GetMatrix(jRank));
      return IsZeroGmoduleVector(TheProd);
    fi;
  end;
  DoHomotopy:=function(jRank, TheVector)
    local TheDimRet, TheDimInput, TheReturn, iCol, TheRec, iElt, eVal, eElt, fElt, pos, eImg, eEnt, eSign, jCol, jElt, ePreElt, fPreElt, fVal, pos2, TheProd, test;
    TheDimRet:=TheResol!.dimension(jRank+1);
    TheDimInput:=TheResol!.dimension(jRank);
    if TheDimInput<>Length(TheVector) then
      Error("You are not correct");
    fi;
    TheReturn:=GMOD_GetZeroVector(TheDimRet);
    for iCol in [1..TheDimInput]
    do
      TheRec:=TheVector[iCol];
      for iElt in [1..Length(TheRec.ListVal)]
      do
        eVal:=TheRec.ListVal[iElt];
        eElt:=TheRec.ListElt[iElt];
        fElt:=eElt^(-1);
        pos:=Position(TheResol!.elts, fElt);
        eImg:=TheResol!.homotopy(jRank, [iCol, pos]);
        for eEnt in eImg
        do
          eSign:=SignInt(eEnt[1]);
          jCol:=AbsInt(eEnt[1]);
          jElt:=eEnt[2];
          ePreElt:=TheResol!.elts[jElt];
          fPreElt:=ePreElt^(-1);
          fVal:=eVal*eSign;
          pos2:=Position(TheReturn[jCol].ListElt, fPreElt);
          if pos2=fail then
            Add(TheReturn[jCol].ListVal, fVal);
            Add(TheReturn[jCol].ListElt, fPreElt);
          else
            TheReturn[jCol].ListVal[pos2]:=TheReturn[jCol].ListVal[pos2]+fVal;
          fi;
        od;
      od;
    od;
    TheProd:=VectorMatrixGmoduleMultiplication(TheReturn, GetMatrix(jRank+1));
    test:=IsEqualGmoduleVector(TheProd,TheVector);
    if test=false then
      Error("Non correct homotopy computation");
    fi;
    return TheReturn;
  end;
  GetMatrix:=function(jRank)
    local TheDim1, TheDim2, TheMat, iLine, eLine, iCol, eImg, eEnt, eSign, eElt, fElt, pos;
    TheDim1:=TheResol!.dimension(jRank);
    TheDim2:=TheResol!.dimension(jRank-1);
    TheMat:=[];
    for iLine in [1..TheDim1]
    do
      eLine:=GMOD_GetZeroVector(TheDim2);
      eImg:=TheResol!.boundary(jRank,iLine);
      for eEnt in eImg
      do
        eSign:=SignInt(eEnt[1]);
        iCol:=AbsInt(eEnt[1]);
        eElt:=TheResol!.elts[eEnt[2]];
        fElt:=eElt^(-1);
        pos:=Position(eLine[iCol].ListElt, fElt);
        if pos=fail then
          Add(eLine[iCol].ListVal, eSign);
          Add(eLine[iCol].ListElt, fElt);
        else
          eLine[iCol].ListVal[pos]:=eLine[iCol].ListVal[pos]+eSign;
        fi;
      od;
      Add(TheMat, eLine);
    od;
    return rec(nbLine:=TheDim1, nbCol:=TheDim2, TheMat:=TheMat);
  end;
  GetDimension:=function(iRank)
    return TheResol!.dimension(iRank);
  end;
  return rec(GetMatrix:=GetMatrix,
             GetDimension:=GetDimension, 
             DoHomotopy:=DoHomotopy,
             IsInKernel:=IsInKernel);
end;

ResolutionComingFromHAP:=function(GRP, kLevel)
  local TheResol;
  TheResol:=ResolutionFiniteGroup(GRP, kLevel);
  return TranslationGAPresolutionPolyhedralResolution(TheResol, GRP, kLevel);
end;



GetAllHomologyClasses:=function(TheMat1, TheMat2, dim1, dim2, dim3)
  local ListVector, ListStatus, FuncInsert, IsFinished, eVect, GetOrderVect, ListOrder, TheKernel, iVect;
  ListVector:=[];
  ListStatus:=[];
  TheKernel:=NullspaceIntMat(TheMat2);
  FuncInsert:=function(eNewVect)
    local eVect;
    for eVect in TheKernel
    do
      if SolutionIntMat(TheKernel, eVect-eNewVect)<>fail then
        return;
      fi;
    od;
    Add(ListVector, eNewVect);
    Add(ListStatus, 1);
  end;
  FuncInsert(ListWithIdenticalEntries(dim2, 0));
  while(true)
  do
    IsFinished:=true;
    for iVect in [1..Length(ListVector)]
    do
      if ListStatus[iVect]=1 then
        ListStatus[iVect]:=0;
        IsFinished:=false;
        for eVect in TheKernel
        do
          FuncInsert(ListVector[iVect]+eVect);
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  GetOrderVect:=function(eVect)
    local TheOrd;
    TheOrd:=1;
    while(true)
    do
      if SolutionIntMat(TheKernel, TheOrd*eVect)<>fail then
        return TheOrd;
      fi;
      TheOrd:=TheOrd+1;
    od;
  end;
  ListOrder:=List(ListVector, GetOrderVect);
  return rec(ListVector:=ListVector, ListOrder:=ListOrder);
end;



SylowSubgroupMapping:=function(PolyhedralTesselation, pSing)
  local NewListOrbitFaces, TheDim, iDim, nbOrb, NewListOrbit, iOrb, TheSylowStab, TheRec;
  NewListOrbitFaces:=[];
  Add(NewListOrbitFaces, PolyhedralTesselation.ListOrbitByRank[1]);
  TheDim:=Length(PolyhedralTesselation.ListOrbitByRank);
  for iDim in [2..TheDim]
  do
    nbOrb:=Length(PolyhedralTesselation.ListOrbitByRank[iDim]);
    NewListOrbit:=[];
    for iOrb in [1..nbOrb]
    do
      TheSylowStab:=SylowSubgroup(PolyhedralTesselation.ListOrbitByRank[iDim][iOrb].TheStab, pSing);
      TheRec:=rec(TheStab:=TheSylowStab, BoundaryImage:=PolyhedralTesselation.ListOrbitByRank[iDim][iOrb].BoundaryImage);
      Add(NewListOrbit, TheRec);
    od;
    Add(NewListOrbitFaces, NewListOrbit);
  od;
  return rec(ListOrbitByRank:=NewListOrbitFaces, IdentityElt:=PolyhedralTesselation.IdentityElt);
end;




GetStabilizersAndSubgroups:=function(TheBoundary)
  local len, TotalListGroupPairs, iRank, nbFace, iFace, ListSubgroups, TheMatrixStab, NewListGens, TheSubgroup, FuncInsert, eElt, ListSmallGens, TheRotSubgroup;
  len:=Length(TheBoundary.ListOrbitByRank);
  TotalListGroupPairs:=[];
  for iRank in [0..len-2]
  do
    nbFace:=Length(TheBoundary.ListOrbitByRank[iRank+2]);
    ListSubgroups:=[];
    for iFace in [1..nbFace]
    do
      TheMatrixStab:=TheBoundary.ListOrbitByRank[iRank+2][iFace].TheStab;
      NewListGens:=[];
      TheSubgroup:=Group([TheBoundary.IdentityElt]);
      FuncInsert:=function(eElt)
        if TheBoundary.FuncSignatureDet(iRank, iFace, eElt)=1 then
          if eElt in TheSubgroup then
            return;
          fi;
          Add(NewListGens, eElt);
          TheSubgroup:=Group(NewListGens);
        fi;
      end;
      for eElt in TheMatrixStab
      do
        FuncInsert(eElt);
      od;
      ListSmallGens:=SmallGeneratingSet(TheSubgroup);
      TheRotSubgroup:=Group(ListSmallGens);
      Add(ListSubgroups, rec(TheStab:=TheMatrixStab, TheRotSubgroup:=TheRotSubgroup));
    od;
    Add(TotalListGroupPairs, ListSubgroups);
  od;
  return TotalListGroupPairs;
end;



GetCondensedFormatForBoundary:=function(TheBoundary)
  local TotalListGroupPairs, len, TheCondensedDataBoundary, iRank, nbFace, iFace, ePair, eRec, ListInfos;
  TotalListGroupPairs:=GetStabilizersAndSubgroups(TheBoundary);
  len:=Length(TheBoundary.ListOrbitByRank);
  TheCondensedDataBoundary:=[];
  for iRank in [0..len-2]
  do
    Print("iRank=", iRank, "\n");
    nbFace:=Length(TheBoundary.ListOrbitByRank[iRank+2]);
    ListInfos:=[];
    for iFace in [1..nbFace]
    do
      ePair:=TotalListGroupPairs[iRank+1][iFace];
      eRec:=rec(TheMatrixStab:=ePair.TheStab, TheRotSubgroup:=ePair.TheRotSubgroup, BoundaryImage:=TheBoundary.ListOrbitByRank[iRank+2][iFace].BoundaryImage);
      Add(ListInfos, eRec);
    od;
    Add(TheCondensedDataBoundary, ListInfos);
  od;
  return TheCondensedDataBoundary;
end;

GetStructureDescriptionBoundary:=function(TheDataCondens)
  local ListReturn, TheLen, i, nbOrb, iOrb, eGRP1, eGRP2, ListNewPair, ePair;
  ListReturn:=[];
  TheLen:=Length(TheDataCondens);
  for i in [1..TheLen]
  do
    nbOrb:=Length(TheDataCondens[i]);
    ListNewPair:=[];
    for iOrb in [1..nbOrb]
    do
      eGRP1:=TheDataCondens[i][iOrb].TheMatrixStab;
      eGRP2:=TheDataCondens[i][iOrb].TheRotSubgroup;
      StructureDescription(eGRP1);
      StructureDescription(eGRP2);
      ePair:=rec(TheMatrixStab:=eGRP1, TheRotSubgroup:=eGRP2);
      Add(ListNewPair, ePair);
    od;
    Add(ListReturn, ListNewPair);
  od;
  return ListReturn;
end;






GroupHomologyByCellDecomposition:=function(PolyhedralInformation)
  local kAvailable, MatrixOfDim, ListResolutionsByRank, SpaceCoHomotopyFunction, ListDimensions, ListMatrixDoperators, MatrixBegin, FuncSignatureOperation, FuncSignedMatrix, IsInKernel, IsInKernelFaceCase, DoHomotopy, GetDifferentiation, GetDifferentiationD0, GetDifferentiationD1, GetDifferentiationDi, PreInitialization, Initialization, TheListStatus, GetDimensions, ListStatusDiff, GetDimension, DoSave, SetSave, GetRankLevelDimension, FuncSignatureDet;
  kAvailable:=Length(PolyhedralInformation.ListOrbitByRank)-2;
  FuncSignatureDet:=function(iRank, iFace, eElt)
    if not(eElt in PolyhedralInformation.ListOrbitByRank[iRank+2][iFace].TheStab) then
      Error("The element is not in the Stabilizer");
    fi;
    if eElt in PolyhedralInformation.ListOrbitByRank[iRank+2][iFace].RotationSubgroup then
      return 1;
    fi;
    return -1;
  end;
  DoSave:=true;
  FuncSignatureOperation:=function(iRank, iFace, eGmod)
    local NewListVal, iVal;
    NewListVal:=[];
    for iVal in [1..Length(eGmod.ListVal)]
    do
      Add(NewListVal, eGmod.ListVal[iVal]*FuncSignatureDet(iRank, iFace, eGmod.ListElt[iVal]));
    od;
    return rec(ListVal:=NewListVal, ListElt:=eGmod.ListElt);
  end;
  FuncSignedMatrix:=function(TheResol, iRank, jRank, iFace)
    local TheMatRES, iLine, iCol, TheDim1, TheDim2, RetMat, eLine;
    TheMatRES:=TheResol.GetMatrix(jRank);
    TheDim1:=TheResol.GetDimension(jRank);
    TheDim2:=TheResol.GetDimension(jRank-1);
    RetMat:=[];
    for iLine in [1..TheDim1]
    do
      eLine:=[];
      for iCol in [1..TheDim2]
      do
        Add(eLine, FuncSignatureOperation(iRank, iFace, TheMatRES.TheMat[iLine][iCol]));
      od;
      Add(RetMat, eLine);
    od;
    return rec(nbLine:=TheDim1, nbCol:=TheDim2, TheMat:=RetMat);
  end;
  IsInKernelFaceCase:=function(iRank, jRank, eVect)
    local PrevVal, iFace, TheResol, TheStab, TheDimInput, TheDimOutput, eVectSel, ListRightCoset, iCos, TheVect1, TheVect2, test;
    PrevVal:=0;
    for iFace in [1..Length(PolyhedralInformation.ListOrbitByRank[iRank+2])]
    do
      TheResol:=ListResolutionsByRank[iRank+1][iFace];
      TheStab:=PolyhedralInformation.ListOrbitByRank[iRank+2][iFace].TheStab;
      TheDimInput:=TheResol.GetDimension(jRank);
      TheDimOutput:=TheResol.GetDimension(jRank+1);
      eVectSel:=ReducedGmoduleVector(eVect{[1+PrevVal..PrevVal+TheDimInput]});
      ListRightCoset:=RightCosetVectorExpression(TheStab, eVectSel);
      for iCos in [1..Length(ListRightCoset)]
      do
        TheVect1:=ListRightCoset[iCos].TheVect;
        TheVect2:=List(TheVect1, x->FuncSignatureOperation(iRank, iFace, x));
        if TheResol.IsInKernel(jRank, TheVect2)=false then
          return false;
        fi;
      od;
      PrevVal:=PrevVal+TheDimInput;
    od;
    return true;
  end;
  SpaceCoHomotopyFunction:=function(iRank, jRank, eVect)
    local TheReturn, PrevVal, iFace, TheResol, TheStab, TheDimInput, TheDimOutput, eVectSel, ListRightCoset, iCol, iVal, ListPreImage, iCos, PreImage1, PreImage2, TheReturn2, TheVect1, TheVect2, TotalDimOutput;
    if IsInKernelFaceCase(iRank, jRank, eVect)=false then
      Print("Sorry, the contracting homotopy is only defined in the kernel\n");
      Print("We are aware it is a limitation, but it is in aggreement with\n");
      Print("Our non-respect of Z-linearity\n");
      Error("Please correct your call");
    fi;
    TheReturn:=[];
    PrevVal:=0;
    TotalDimOutput:=MatrixOfDim[iRank+1][jRank+2];
    for iFace in [1..Length(PolyhedralInformation.ListOrbitByRank[iRank+2])]
    do
      TheResol:=ListResolutionsByRank[iRank+1][iFace];
      TheStab:=PolyhedralInformation.ListOrbitByRank[iRank+2][iFace].TheStab;
      TheDimInput:=TheResol.GetDimension(jRank);
      TheDimOutput:=TheResol.GetDimension(jRank+1);
      eVectSel:=ReducedGmoduleVector(eVect{[1+PrevVal..PrevVal+TheDimInput]});
      ListRightCoset:=RightCosetVectorExpression(TheStab, eVectSel);
      ListPreImage:=GMOD_GetZeroVector(TheDimOutput);
      for iCos in [1..Length(ListRightCoset)]
      do
        TheVect1:=ListRightCoset[iCos].TheVect;
        TheVect2:=List(TheVect1, x->FuncSignatureOperation(iRank, iFace, x));
        PreImage2:=TheResol.DoHomotopy(jRank, TheVect2);
        PreImage1:=List(PreImage2, x->FuncSignatureOperation(iRank, iFace, x));
        for iCol in [1..TheDimOutput]
        do
          for iVal in [1..Length(PreImage1[iCol].ListElt)]
          do
            Add(ListPreImage[iCol].ListVal, PreImage1[iCol].ListVal[iVal]);
            Add(ListPreImage[iCol].ListElt, PreImage1[iCol].ListElt[iVal]*ListRightCoset[iCos].eCos);
          od;
        od;
      od;
      if IsEqualGmoduleVector(VectorMatrixGmoduleMultiplication(ListPreImage, FuncSignedMatrix(TheResol, iRank, jRank+1, iFace)), eVectSel)=false then
        Error("Non correct homotopy computation 2");
      fi;
      Append(TheReturn, ListPreImage);
      PrevVal:=PrevVal+TheDimInput;
    od;
    TheReturn2:=ReducedGmoduleVector(TheReturn);
    if IsEqualGmoduleVector(VectorMatrixGmoduleMultiplication(TheReturn2, GetDifferentiationD0(iRank, jRank+1)), eVect)=false then
      Error("Non correct homotopy computation 3");
    fi;
    return TheReturn2;
  end;
  GetDimensions:=function()
    return rec(MatrixOfDim:=MatrixOfDim, MatrixBegin:=MatrixBegin, ListDimensions:=ListDimensions);
  end;
  GetRankLevelDimension:=function(iRank, iLevel)
    local RetDim, iFace, TheDim;
    if IsBound(MatrixOfDim[iRank+1]) then
      if IsBound(MatrixOfDim[iRank+1][iLevel+1]) then
        return MatrixOfDim[iRank+1][iLevel+1];
      fi;
    fi;
    RetDim:=0;
    for iFace in [1..Length(PolyhedralInformation.ListOrbitByRank[iRank+2])]
    do
      TheDim:=ListResolutionsByRank[iRank+1][iFace].GetDimension(iLevel);
      RetDim:=RetDim+TheDim;
    od;
    return RetDim;
  end;
  PreInitialization:=function(kLevel)
    local iRank, ListResol, LevSearch, iFace, eFace, TheStab, TheResol, iLevel, TheDim, PrevVal, iK, jRank, iRankImage, jRankImage, iH1, LDim;
    ListResolutionsByRank:=[];
    MatrixOfDim:=[];
    for iRank in [0..kLevel]
    do
      LDim:=[];
      LevSearch:=kLevel-iRank;
      for iLevel in [0..LevSearch]
      do
        Add(LDim, 0);
      od;
      Add(MatrixOfDim, LDim);
    od;
    Print("Computing the resolutions\n");
    for iRank in [0..kLevel]
    do
      Print("  iRank=", iRank, "\n");
      ListResol:=[];
      LevSearch:=kLevel-iRank;
      for iFace in [1..Length(PolyhedralInformation.ListOrbitByRank[iRank+2])]
      do
        eFace:=PolyhedralInformation.ListOrbitByRank[iRank+2][iFace];
        TheStab:=eFace.TheStab;
        Print("    iFace=", iFace, "  |G|=", Order(TheStab), " dimensions:");
        TheResol:=PolyhedralInformation.GetResolution(TheStab, LevSearch);
        for iLevel in [0..LevSearch]
        do
          TheDim:=TheResol.GetDimension(iLevel);
          Print(" ", TheDim);
          MatrixOfDim[iRank+1][iLevel+1]:=MatrixOfDim[iRank+1][iLevel+1]+TheDim;
        od;
        Print("\n");
        Add(ListResol, TheResol);
      od;
      Add(ListResolutionsByRank, ListResol);
    od;
    ListDimensions:=ListWithIdenticalEntries(kLevel+1,0);
#    ListDimensions[1]:=0;
    for iRank in [0..kLevel]
    do
      LevSearch:=kLevel-iRank;
      for jRank in [0..LevSearch]
      do
        ListDimensions[iRank+jRank+1]:=ListDimensions[iRank+jRank+1]+MatrixOfDim[iRank+1][jRank+1];
      od;
    od;
    MatrixBegin:=NullMat(kLevel+1, kLevel+1);
    for iRank in [0..kLevel]
    do
      PrevVal:=0;
      for iH1 in [0..iRank]
      do
        iRankImage:=iRank-iH1;
        jRankImage:=iH1;
        MatrixBegin[iRankImage+1][jRankImage+1]:=PrevVal;
        PrevVal:=PrevVal+MatrixOfDim[iRankImage+1][jRankImage+1];
      od;
    od;
    for iRank in [0..kLevel]
    do
      LevSearch:=kLevel-iRank;
      for jRank in [0..LevSearch]
      do
        Print(" ", MatrixOfDim[iRank+1][jRank+1]);
      od;
      Print("\n");
    od;
    TheListStatus:=[];
    for iK in [0..kLevel]
    do
      Add(TheListStatus, NullMat(kLevel+1, kLevel+1));
    od;
    ListMatrixDoperators:=[];
    ListStatusDiff:=[];
    for iK in [1..kLevel]
    do
      Add(ListMatrixDoperators, GMOD_GetZeroMatrix(ListDimensions[iK+1],ListDimensions[iK]));
      Add(ListStatusDiff, 0);
    od;
  end;
  Initialization:=function(kLevel)
    local TheMat, iRank;
#    Print("Call Initialization for kLevel=", kLevel, "\n");
    PreInitialization(kLevel);
    for iRank in [1..kLevel]
    do
      TheMat:=GetDifferentiation(iRank);
    od;
  end;
  SetSave:=function(TheStatus)
    SetSave:=TheStatus;
  end;
  GetDimension:=function(iRank)
    return ListDimensions[iRank+1];
  end;
  GetDifferentiationD0:=function(iRank, iLevel)
    local dimSource, dimTarget, BeginSource, BeginTarget, eBeginSource, eBeginTarget, eEndSource, eEndTarget, PrevVal1, PrevVal2, TheMatReturn, iFace, TheResol, TheDim1, TheDim2, TheMatRES, iLine, iCol;
    if iLevel<=0 then
      Error("Wrong call to the function");
    fi;
    dimSource:=GetRankLevelDimension(iRank, iLevel);
    dimTarget:=GetRankLevelDimension(iRank, iLevel-1);
    if DoSave=true then
      BeginSource:=MatrixBegin[iRank+1][iLevel+1];
      BeginTarget:=MatrixBegin[iRank+1][iLevel];
      eBeginSource:=BeginSource+1;
      eBeginTarget:=BeginTarget+1;
      eEndSource:=BeginSource+dimSource;
      eEndTarget:=BeginTarget+dimTarget;
      if TheListStatus[1][iRank+1][iLevel+1]=1 then
        return rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=List(ListMatrixDoperators[iRank+iLevel].TheMat{[eBeginSource..eEndSource]}, x->x{[eBeginTarget..eEndTarget]}));
      fi;
    fi;
    Print("Getting D0: iRank=", iRank, " iLevel=", iLevel, "\n");
    PrevVal1:=0;
    PrevVal2:=0;
    TheMatReturn:=GMOD_GetZeroMatrix(dimSource, dimTarget);
    for iFace in [1..Length(PolyhedralInformation.ListOrbitByRank[iRank+2])]
    do
      TheResol:=ListResolutionsByRank[iRank+1][iFace];
      TheDim1:=TheResol.GetDimension(iLevel);
      TheDim2:=TheResol.GetDimension(iLevel-1);
      TheMatRES:=FuncSignedMatrix(TheResol, iRank, iLevel, iFace);
      for iLine in [1..TheDim1]
      do
        TheMatReturn.TheMat[PrevVal1+iLine]{[PrevVal2+1..PrevVal2+TheDim2]}:=TheMatRES.TheMat[iLine];
      od;
      PrevVal1:=PrevVal1+TheDim1;
      PrevVal2:=PrevVal2+TheDim2;
    od;
    if DoSave=true then
      TheListStatus[1][iRank+1][iLevel+1]:=1;
      for iLine in [1..dimSource]
      do
        for iCol in [1..dimTarget]
        do
          ListMatrixDoperators[iRank+iLevel].TheMat[iLine+BeginSource][iCol+BeginTarget]:=TheMatReturn.TheMat[iLine][iCol];
        od;
      od;
    fi;
    return TheMatReturn;
  end;
  GetDifferentiationD1:=function(iRank, iLevel)
    local dimSource, dimTarget, BeginSource, BeginTarget, eBeginSource, eBeginTarget, eEndSource, eEndTarget, TheMat, iOrbit, TheImage, TheBoundary, iEnt, iFace, eSign, eElt, TheProd, TheOpp, TheMatReturn, iLine, iCol;
    if iRank<=0 then
      Error("Error, we do not do differentiation D1 at iRank=0");
    fi;
    dimSource:=GetRankLevelDimension(iRank, iLevel);
    dimTarget:=GetRankLevelDimension(iRank-1, iLevel);
    if DoSave=true then
      BeginSource:=MatrixBegin[iRank+1][iLevel+1];
      BeginTarget:=MatrixBegin[iRank][iLevel+1];
      eBeginSource:=BeginSource+1;
      eBeginTarget:=BeginTarget+1;
      eEndSource:=BeginSource+dimSource;
      eEndTarget:=BeginTarget+dimTarget;
      if TheListStatus[2][iRank+1][iLevel+1]=1 then
        return rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=List(ListMatrixDoperators[iRank+iLevel].TheMat{[eBeginSource..eEndSource]}, x->x{[eBeginTarget..eEndTarget]}));
      fi;
    fi;
    Print("Getting D1: iRank=", iRank, " iLevel=", iLevel, "\n");
    if iLevel=0 then
      TheMat:=[];
      for iOrbit in [1..dimSource]
      do
        TheImage:=GMOD_GetZeroVector(dimTarget);
        TheBoundary:=PolyhedralInformation.ListOrbitByRank[iRank+2][iOrbit].BoundaryImage;
        for iEnt in [1..Length(TheBoundary.ListSign)]
        do
          iFace:=TheBoundary.ListIFace[iEnt];
          eSign:=TheBoundary.ListSign[iEnt];
          eElt:=TheBoundary.ListElt[iEnt];
          Add(TheImage[iFace].ListVal, eSign);
          Add(TheImage[iFace].ListElt, eElt);
        od;
        Add(TheMat, TheImage);
      od;
    else
      TheProd:=MatrixMatrixGmoduleMultiplication(GetDifferentiationD0(iRank, iLevel), GetDifferentiationD1(iRank, iLevel-1));
      TheOpp:=MatrixGmoduleOpposite(TheProd);
      TheMat:=List(TheOpp.TheMat, x->SpaceCoHomotopyFunction(iRank-1, iLevel-1, x));
    fi;
    TheMatReturn:=rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=TheMat);
    if DoSave=true then
      TheListStatus[2][iRank+1][iLevel+1]:=1;
      for iLine in [1..dimSource]
      do
        for iCol in [1..dimTarget]
        do
          ListMatrixDoperators[iRank+iLevel].TheMat[iLine+BeginSource][iCol+BeginTarget]:=TheMat[iLine][iCol];
        od;
      od;
    fi;
    return TheMatReturn;
  end;
  GetDifferentiationDi:=function(iRank, iLevel, i)
    local dimSource, dimTarget, BeginSource, BeginTarget, eBeginSource, eBeginTarget, eEndSource, eEndTarget, dimTargetPrev, ThePrevBigMat, iH, eMat1, eMat2, eProd, TheOpp, TheMat, TheMatReturn, iLine, iCol;
    if i=0 then
      return GetDifferentiationD0(iRank, iLevel);
    fi;
    if i=1 then
      return GetDifferentiationD1(iRank, iLevel);
    fi;
    dimSource:=GetRankLevelDimension(iRank, iLevel);
    dimTarget:=GetRankLevelDimension(iRank-i, iLevel+i-1);
    if DoSave=true then
      BeginSource:=MatrixBegin[iRank+1][iLevel+1];
      BeginTarget:=MatrixBegin[iRank+1-i][iLevel+i];
      eBeginSource:=BeginSource+1;
      eBeginTarget:=BeginTarget+1;
      eEndSource:=BeginSource+dimSource;
      eEndTarget:=BeginTarget+dimTarget;
      if TheListStatus[i+1][iRank+1][iLevel+1]=1 then
        return rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=List(ListMatrixDoperators[iRank+iLevel].TheMat{[eBeginSource..eEndSource]}, x->x{[eBeginTarget..eEndTarget]}));
      fi;
    fi;
    Print("Getting Di: i=", i, " iRank=", iRank, " iLevel=", iLevel, "\n");
    dimTargetPrev:=MatrixOfDim[iRank+1-i][iLevel+i-1];
    ThePrevBigMat:=GMOD_GetZeroMatrix(dimSource, dimTargetPrev);
    for iH in [0..i-1]
    do
      if i-iH>=0 and iLevel-1+iH >=0 then
        eMat1:=GetDifferentiationDi(iRank, iLevel, iH);
        eMat2:=GetDifferentiationDi(iRank-iH, iLevel-1+iH, i-iH);
        eProd:=MatrixMatrixGmoduleMultiplication(eMat1, eMat2);
        ThePrevBigMat:=MatrixGmoduleAddition(ThePrevBigMat, eProd);
      fi;
    od;
    TheOpp:=MatrixGmoduleOpposite(ThePrevBigMat);
    TheMat:=List(TheOpp.TheMat, x->SpaceCoHomotopyFunction(iRank-i, iLevel-2+i, x));
    TheMatReturn:=rec(nbLine:=dimSource, nbCol:=dimTarget, TheMat:=TheMat);
    if DoSave=true then
      TheListStatus[i+1][iRank+1][iLevel+1]:=1;
      for iLine in [1..dimSource]
      do
        for iCol in [1..dimTarget]
        do
          ListMatrixDoperators[iRank+iLevel].TheMat[iLine+BeginSource][iCol+BeginTarget]:=TheMat[iLine][iCol];
        od;
      od;
    fi;
    return TheMatReturn;
  end;
  GetDifferentiation:=function(kLevel)
    local iComp, eMat, iH;
    if ListStatusDiff[kLevel]=0 then
      ListStatusDiff[kLevel]:=1;
      for iComp in [0..kLevel]
      do
        for iH in [0..kLevel]
        do
          if (iComp + iH <= kLevel and iH>0) or (iComp > 0 and iH=0) then
            eMat:=GetDifferentiationDi(kLevel-iComp, iComp, iH);
          fi;
        od;
      od;
    fi;
    return ListMatrixDoperators[kLevel];
  end;
  # the obtained resolution is NOT twisted, the
  # kernel is the set $S$
  # x=sum alpha_g g    with   sum alpha_g=0
  IsInKernel:=function(iLevel, TheVector)
    local eVal, TheProd;
    if iLevel=0 then
      eVal:=TheVector[1];
      return Sum(eVal.ListVal)=0;
    else
      TheProd:=VectorMatrixGmoduleMultiplication(TheVector, ListMatrixDoperators[iLevel+1]);
      return IsZeroGmoduleVector(TheProd);
    fi;
  end;
  DoHomotopy:=function(iRank, TheVector)
    local ThePreImage, ListVectorComponents, iH, iRankSource, jRankSource, TheDim, TheBegin, TheReturn, iRankPre, jRankPre, iH2, TheImg, TheProd, test, iRankImage, jRankImage;
    ListVectorComponents:=[];
    for iH in [0..iRank]
    do
      iRankSource:=iRank-iH;
      jRankSource:=iH;
      TheDim:=MatrixOfDim[iRankSource+1][jRankSource+1];
      TheBegin:=MatrixBegin[iRankSource+1][jRankSource+1];
      Add(ListVectorComponents, TheVector{[TheBegin+1..TheBegin+TheDim+1]});
    od;
    TheReturn:=[];
    for iH in [0..iRank+1]
    do
      iRankPre:=iRank+1-iH;
      jRankPre:=iH;
      if iH=0 then
        ThePreImage:=PolyhedralInformation.DoHomotopy(iRank, ListVectorComponents[1]);
      else
        ThePreImage:=SpaceCoHomotopyFunction(iRank-(iH-1), iH-1, ListVectorComponents[iH]);
      fi;
      Append(TheReturn, ThePreImage);
      for iH2 in [0..iRank+1]
      do
        iRankImage:=iRank+1-iH2;
        jRankImage:=iH2-1;
        if iRankImage>=0 and jRankImage>=0 then
          TheImg:=VectorMatrixGmoduleMultiplication(ThePreImage, GetDifferentiationDi(iRankPre, jRankPre, iH2));
          ListVectorComponents[jRankImage+1]:=VectorGmoduleAddition(ListVectorComponents[jRankImage+1], VectorGmoduleOpposite(TheImg));
        fi;
      od;
    od;
    TheProd:=VectorMatrixGmoduleMultiplication(TheReturn, ListMatrixDoperators[iRank+1]);
    test:=IsEqualGmoduleVector(TheProd, TheVector);
    if test=false then
      Error("Non correct homotopy computation CTC wall");
    fi;
    return TheReturn;
  end;
  return rec(GetDifferentiation:=GetDifferentiation, 
             GetDifferentiationDi:=GetDifferentiationDi, 
             GetDifferentiationD1:=GetDifferentiationD1, 
             GetDifferentiationD0:=GetDifferentiationD0, 
             Initialization:=Initialization, 
             PreInitialization:=PreInitialization, 
             GetDimension:=GetDimension, 
             DoHomotopy:=DoHomotopy, 
             IsInKernel:=IsInKernel, 
             GetDimensions:=GetDimensions);
end;


StatisticalInformationOnMatrices:=function(MyKindOfResolution)
  local nbMatrix, iMatrix, MaxCoefficient, SumCoefficient, MaxNbEntry, SumNbEntry, eLine, eEnt, ListAbsVal, TheMax, MaxLocCoefficient;
  nbMatrix:=Length(MyKindOfResolution);
  for iMatrix in [1..nbMatrix]
  do
    MaxCoefficient:=0;
    SumCoefficient:=0;
    MaxNbEntry:=0;
    SumNbEntry:=0;
    MaxLocCoefficient:=0;
    for eLine in MyKindOfResolution[iMatrix].TheMat
    do
      for eEnt in eLine
      do
        ListAbsVal:=List(eEnt.ListVal, AbsInt);
        if Length(ListAbsVal)=0 then
          TheMax:=0;
        else
          TheMax:=Maximum(ListAbsVal);
        fi;
        MaxCoefficient:=Maximum(MaxCoefficient, TheMax);
        SumCoefficient:=SumCoefficient+Sum(ListAbsVal);
        MaxLocCoefficient:=Maximum(MaxLocCoefficient, Sum(ListAbsVal));
        MaxNbEntry:=Maximum(MaxNbEntry, Length(ListAbsVal));
        SumNbEntry:=SumNbEntry+Length(ListAbsVal);
      od;
    od;
    Print("iMatrix=", iMatrix, "/", nbMatrix, " nbLine=", MyKindOfResolution[iMatrix].nbLine, " nbCol=", 
MyKindOfResolution[iMatrix].nbCol, "\n");
    Print("    MaxCoefficient=", MaxCoefficient, " SumCoefficient=", SumCoefficient, "\n");
    Print("    MaxNbEntry=", MaxNbEntry, " SumNbEntry=", SumNbEntry, "\n");
    Print("    MaxLocCoefficient=", MaxLocCoefficient, "\n");
  od;
end;


GmoduleMatrixToZmatrix:=function(TheMat)
  local nbLine, nbCol, NewMat, iLine, eLine, iCol;
  nbLine:=TheMat.nbLine;
  nbCol:=TheMat.nbCol;
  NewMat:=[];
  for iLine in [1..nbLine]
  do
    Add(NewMat, List(TheMat.TheMat[iLine], x->Sum(x.ListVal)));
  od;
  return NewMat;
end;

GmoduleMatrixToZmatrixRepresentation:=function(TheMat, TheRepresentation)
  local nbLine, nbCol, NewMat, iLine, eLine, iCol, eSumMat, eGmodule, iEnt, nbEnt, dimRepr, i, j;
  nbLine:=TheMat.nbLine;
  nbCol:=TheMat.nbCol;
  dimRepr:=TheRepresentation.dimRepr;
  NewMat:=NullMat(nbLine*dimRepr, nbCol*dimRepr);
  for iLine in [1..nbLine]
  do
    for iCol in [1..nbCol]
    do
      eGmodule:=TheMat.TheMat[iLine][iCol];
      eSumMat:=NullMat(dimRepr, dimRepr);
      nbEnt:=Length(eGmodule.ListVal);
      for iEnt in [1..nbEnt]
      do
        eSumMat:=eSumMat + eGmodule.ListVal[iEnt]*TheRepresentation.FuncImage(eGmodule.ListElt[iEnt]);
      od;
      for i in [1..dimRepr]
      do
        for j in [1..dimRepr]
        do
          NewMat[(iLine-1)*dimRepr+i][(iCol-1)*dimRepr+j]:=eSumMat[i][j];
        od;
      od;
    od;
  od;
  return NewMat;
end;





GettingHomologies:=function(MyKindOfResolution)
  local kSought, ListDimensions, iRank, ListMatrixDoperators, TheHomology;
  Print("Killing the G-action\n");
  kSought:=Length(MyKindOfResolution)-2;
  ListDimensions:=[];
  for iRank in [1..kSought+2]
  do
    if iRank=1 then
      Add(ListDimensions, MyKindOfResolution[iRank].nbCol);
    fi;
    Add(ListDimensions, MyKindOfResolution[iRank].nbLine);
  od;
  ListMatrixDoperators:=List(MyKindOfResolution, GmoduleMatrixToZmatrix);
  # now computing the homologies
  Print("At last the homologies\n");
  return GettingHomologiesFromKilledMatrices(ListDimensions, ListMatrixDoperators);
end;


GettingHomologiesOfRepresentation:=function(MyKindOfResolution, TheRepresentation)
  local kSought, ListDimensions, iRank, ListMatrixDoperators, TheHomology;
  Print("Killing the G-action\n");
  kSought:=Length(MyKindOfResolution)-2;
  ListDimensions:=[];
  for iRank in [1..kSought+2]
  do
    if iRank=1 then
      Add(ListDimensions, MyKindOfResolution[iRank].nbCol);
    fi;
    Add(ListDimensions, MyKindOfResolution[iRank].nbLine);
  od;
  ListMatrixDoperators:=List(MyKindOfResolution, x->GmoduleMatrixToZmatrixRepresentation(x, TheRepresentation));
  # now computing the homologies
  Print("At last the homologies\n");
  return GettingHomologiesFromKilledMatrices(ListDimensions, ListMatrixDoperators);
end;


ApplyTwistingOnRepresentation:=function(ListMat, FuncDet)
  local ListMatSigned, eMatSigned, eLine, eLineSigned, eCol, NewListVal, len, i, eNewVal, eColSigned, eMat;
  ListMatSigned:=[];
  for eMat in ListMat
  do
    eMatSigned:=[];
    for eLine in eMat.TheMat
    do
      eLineSigned:=[];
      for eCol in eLine
      do
        NewListVal:=[];
        len:=Length(eCol.ListVal);
        for i in [1..len]
        do
          eNewVal:=eCol.ListVal[i]*FuncDet(eCol.ListElt[i]);
          Add(NewListVal, eNewVal);
        od;
        eColSigned:=rec(ListVal:=NewListVal, ListElt:=eCol.ListElt);
        Add(eLineSigned, eColSigned);
      od;
      Add(eMatSigned, eLineSigned);
    od;
    Add(ListMatSigned, rec(nbLine:=eMat.nbLine, nbCol:=eMat.nbCol, TheMat:=eMatSigned));
  od;
  return ListMatSigned;
end;



KillFacesWithOrientationReversing_Homology:=function(TheBound)
  local ListRecord, len, iRank, nbOrbit, ListStatus, ListCorresp, iOrbit, ListMat, TheMat, ListIdxSel, iLine, nbLine, iCol, nbCol, iLineOrbit, iColOrbit, eVal, eBound, lenBound, eStatus, eRecord, eOrbit, ListDimensions, TheDim;
  ListRecord:=[];
  len:=Length(TheBound.ListOrbitByRank);
  ListDimensions:=[];
  for iRank in [0..len-2]
  do
    nbOrbit:=Length(TheBound.ListOrbitByRank[iRank+2]);
    ListStatus:=[];
    ListCorresp:=[];
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=TheBound.ListOrbitByRank[iRank+2][iOrbit];
      if eOrbit.TheStab=eOrbit.RotationSubgroup then
        eStatus:=1;
      else
        eStatus:=0;
      fi;
      if eStatus=1 then
        Add(ListCorresp, iOrbit);
      fi;
      Add(ListStatus, eStatus);
    od;
    TheDim:=Sum(ListStatus);
    eRecord:=rec(iRank:=iRank, ListStatus:=ListStatus, ListCorresp:=ListCorresp, TheDimRed:=TheDim);
    Add(ListDimensions, TheDim);
    Add(ListRecord, eRecord);
  od;
  ListMat:=[];
  for iRank in [1..len-2]
  do
    nbLine:=ListRecord[iRank+1].TheDimRed;
    nbCol:=ListRecord[iRank].TheDimRed;
    TheMat:=NullMat(nbLine, nbCol);
    for iLine in [1..nbLine]
    do
      iLineOrbit:=ListRecord[iRank+1].ListCorresp[iLine];
      eBound:=TheBound.ListOrbitByRank[iRank+2][iLineOrbit].BoundaryImage;
      lenBound:=Length(eBound.ListSign);
      for iCol in [1..nbCol]
      do
        iColOrbit:=ListRecord[iRank].ListCorresp[iCol];
        ListIdxSel:=Filtered([1..lenBound], x->eBound.ListIFace[x]=iColOrbit);
        eVal:=Sum(eBound.ListSign{ListIdxSel});
        TheMat[iLine][iCol]:=eVal;
      od;
    od;
    Add(ListMat, TheMat);
  od;
  return GettingHomologiesFromKilledMatrices(ListDimensions, ListMat);
end;



KillFacesWithOrientationReversing_CohomologyKernel:=function(TheBound)
  local ListRecord, len, iRank, nbOrbit, ListStatus, ListCorresp, iOrbit, ListMat, TheMat, ListIdxSel, iLine, nbLine, iCol, nbCol, iLineOrbit, iColOrbit, eVal, eBound, lenBound, eStatus, eRecord, eOrbit, ListDimensions, TheDim, eEnt, ListEntries, ListCol, ListVal, eEntry;
  ListRecord:=[];
  len:=Length(TheBound.ListOrbitByRank);
  ListDimensions:=[];
  for iRank in [1..len]
  do
    nbOrbit:=Length(TheBound.ListOrbitByRank[iRank]);
    ListStatus:=[];
    ListCorresp:=[];
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=TheBound.ListOrbitByRank[iRank][iOrbit];
      if eOrbit.TheStab=eOrbit.RotationSubgroup then
        eStatus:=1;
      else
        eStatus:=0;
      fi;
      if eStatus=1 then
        Add(ListCorresp, iOrbit);
      fi;
      Add(ListStatus, eStatus);
    od;
    TheDim:=Sum(ListStatus);
    eRecord:=rec(iRank:=iRank, ListStatus:=ListStatus, ListCorresp:=ListCorresp, TheDimRed:=TheDim);
    Add(ListDimensions, TheDim);
    Add(ListRecord, eRecord);
  od;
  ListMat:=[];
  for iRank in [1..len-1]
  do
    nbLine:=ListRecord[iRank].TheDimRed;
    nbCol:=ListRecord[iRank+1].TheDimRed;
    ListEntries:=[];
    for iLine in [1..nbLine]
    do
      ListCol:=[];
      ListVal:=[];
      iLineOrbit:=ListRecord[iRank].ListCorresp[iLine];
      eBound:=TheBound.ListOrbitByRank[iRank][iLineOrbit].BoundaryImage;
      lenBound:=Length(eBound.ListSign);
      for iCol in [1..nbCol]
      do
        iColOrbit:=ListRecord[iRank+1].ListCorresp[iCol];
        ListIdxSel:=Filtered([1..lenBound], x->eBound.ListIFace[x]=iColOrbit);
        eVal:=Sum(eBound.ListSign{ListIdxSel});
        if eVal<>0 then
          Add(ListCol, iCol);
          Add(ListVal, eVal);
        fi;
      od;
      eEntry:=rec(ListCol:=ListCol, ListVal:=ListVal);
      Add(ListEntries, eEntry);
    od;
    TheMat:=rec(nbLine:=nbLine, nbCol:=nbCol, ListEntries:=ListEntries);
    Add(ListMat, TheMat);
  od;
  return rec(ListDimensions:=ListDimensions, ListMat:=ListMat);
end;

KillFacesWithOrientationReversing_Cohomology:=function(TheBound)
  local RecCoho;
  RecCoho:=KillFacesWithOrientationReversing_CohomologyKernel(TheBound);
  return GettingCohomologiesFromKilledMatrices(RecCoho.ListDimensions, RecCoho.ListMat);
end;

KillFacesWithOrientationReversing_CohomologyInput:=function(TheBound)
  local RecMatrix;
  RecMatrix:=KillFacesWithOrientationReversing_CohomologyKernel(TheBound);
  return GettingRecMatricesFromKilledMatrices_coho(RecMatrix.ListDimensions, RecMatrix.ListMat);
end;



SplitResolutionByFiniteIndexSubgroup:=function(TheResolution, TheGroup, TheSplitFct)
  local ListRightCoset, ListLeftCoset, nbCoset, GetLeftCosetPosition, ListMatrix, eMatrix, nbLine, nbCol, nbLineB, nbColB, eNewMatrix, idx, iLine, iCol, pos, NewPos, eProd, eVal, i, len, iCos, eNewElt, ListDimensions, iMatrix, nbMatrix;
  ListRightCoset:=GetCosetsBySplittingFunction(TheGroup, TheSplitFct).ListCoset;
  ListLeftCoset:=List(ListRightCoset, x->Inverse(x));
  nbCoset:=Length(ListRightCoset);
  Print("nbCoset=", nbCoset, "\n");
  GetLeftCosetPosition:=function(eElt)
    local iCos, InvElt;
    InvElt:=Inverse(eElt);
    for iCos in [1..Length(ListLeftCoset)]
    do
      if TheSplitFct(InvElt*ListLeftCoset[iCos])=true then
        return iCos;
      fi;
    od;
    Error("We should never be there in the first place");
  end;
  ListDimensions:=[];
  ListMatrix:=[];
  nbMatrix:=Length(TheResolution);
  for iMatrix in [1..nbMatrix]
  do
    Print("Building split matrix iMatrix=", iMatrix, "/", nbMatrix, "\n");
    eMatrix:=TheResolution[iMatrix];
    nbLine:=eMatrix.nbLine;
    nbCol:=eMatrix.nbCol;
    nbLineB:=nbLine*nbCoset;
    nbColB:=nbCol*nbCoset;
    Print("  nbLine=", nbLine, " nbCol=", nbCol, " nbLineB=", nbLineB, " nbColB=", nbColB, "\n");
    if iMatrix=1 then
      Add(ListDimensions, nbColB);
    fi;
    Add(ListDimensions, nbLineB);
    eNewMatrix:=NullMat(nbLineB, nbColB);
    idx:=0;
    for iLine in [1..nbLine]
    do
      for iCos in [1..nbCoset]
      do
        idx:=idx+1;
        for iCol in [1..nbCol]
        do
          len:=Length(eMatrix.TheMat[iLine][iCol].ListVal);
          for i in [1..len]
          do
            eProd:=eMatrix.TheMat[iLine][iCol].ListElt[i]*ListLeftCoset[iCos];
            eVal:=eMatrix.TheMat[iLine][iCol].ListVal[i];
            pos:=GetLeftCosetPosition(eProd);
            eNewElt:=Inverse(ListLeftCoset[pos])*eProd;
            NewPos:=(iCol-1)*nbCoset + pos;
            eNewMatrix[idx][NewPos]:=eNewMatrix[idx][NewPos]+eVal;
          od;
        od;
      od;
    od;
    Add(ListMatrix, eNewMatrix);
  od;
  Print("All matrices have been built\n");
  return GettingHomologiesFromKilledMatrices(ListDimensions, ListMatrix);
end;






#
# that is a quite expensive computation actually
CheckVanishingGmoduleResolution:=function(ListMatrix)
  local nbMatrix, iMat, TheMat1, TheMat2, TheProd, test;
  nbMatrix:=Length(ListMatrix);
  for iMat in [1..nbMatrix-1]
  do
    TheMat1:=ListMatrix[iMat];
    TheMat2:=ListMatrix[iMat+1];
    TheProd:=MatrixMatrixGmoduleMultiplication(TheMat2, TheMat1);
    test:=IsZeroGmoduleMatrix(TheProd);
    if test=false then
      return false;
    fi;
  od;
  return true;
end;


PrintBoundaryDescription:=function(TheBound)
  local len, iRank, nbOrb, iOrb, TheStabSize, TheBoundSize, DoCheckSquare, ListCompleteIndex, ListCompleteValue, ListCompleteElement, FuncInsert, iBound, iOrbM1, eEltM1, eSignM1, iOrbM2, eEltM2, eSignM2, eVal, eElt, len2, iBound2, FuncSignatureDet;
  len:=Length(TheBound.ListOrbitByRank)-1;
  FuncSignatureDet:=function(iRank, iFace, eElt)
    if not(eElt in TheBound.ListOrbitByRank[iRank+2][iFace].TheStab) then
      Error("The element is not in the Stabilizer");
    fi;
    if eElt in TheBound.ListOrbitByRank[iRank+2][iFace].RotationSubgroup then
      return 1;
    fi;
    return -1;
  end;
  DoCheckSquare:=false;
  for iRank in [2..len]
  do
    Print("iRank=", iRank-2, "\n");
    nbOrb:=Length(TheBound.ListOrbitByRank[iRank]);
    for iOrb in [1..nbOrb]
    do
      TheStabSize:=Order(TheBound.ListOrbitByRank[iRank][iOrb].TheStab);
      TheBoundSize:=Length(TheBound.ListOrbitByRank[iRank][iOrb].BoundaryImage.ListIFace);
      Print("  iOrb=", iOrb, "/", nbOrb, " |Stab|=", TheStabSize, " |Bound|=", TheBoundSize, "\n");
      if iRank>=3 and DoCheckSquare=true then
        # we checked that boundary square to zero
        ListCompleteIndex:=[];
        ListCompleteValue:=[];
        ListCompleteElement:=[];
        FuncInsert:=function(iOrbIdx, eVal, eElt)
          local lenCase, iCase, eQuot, eSign;
          lenCase:=Length(ListCompleteIndex);
          for iCase in [1..lenCase]
          do
            if ListCompleteIndex[iCase]=iOrbIdx then
              eQuot:=ListCompleteElement[iCase]*Inverse(eElt);
              if eQuot in TheBound.ListOrbitByRank[iRank-2][iOrbIdx].TheStab then
                eSign:=FuncSignatureDet(iRank-4, iOrbIdx, eQuot);
                ListCompleteValue[iCase]:=ListCompleteValue[iCase]+eSign*eVal;
              fi;
            fi;
          od;
          Add(ListCompleteIndex, iOrbIdx);
          Add(ListCompleteValue, eVal);
          Add(ListCompleteElement, eElt);
        end;
        for iBound in [1..TheBoundSize]
        do
          iOrbM1:=TheBound.ListOrbitByRank[iRank][iOrb].BoundaryImage.ListIFace[iBound];
          eEltM1:=TheBound.ListOrbitByRank[iRank][iOrb].BoundaryImage.ListElement[iBound];
          eSignM1:=TheBound.ListOrbitByRank[iRank][iOrb].BoundaryImage.ListSign[iBound];
          len2:=Length(TheBound.ListOrbitByRank[iRank-1][iOrbM1].BoundaryImage.ListIFace);
          for iBound2 in [1..len2]
          do
            iOrbM2:=TheBound.ListOrbitByRank[iRank-1][iOrbM1].BoundaryImage.ListIFace[iBound2];
            eEltM2:=TheBound.ListOrbitByRank[iRank-1][iOrbM1].BoundaryImage.ListElement[iBound2];
            eSignM2:=TheBound.ListOrbitByRank[iRank-1][iOrbM1].BoundaryImage.ListSign[iBound2];
            eVal:=eSignM1*eSignM2;
            eElt:=eEltM1*eEltM2;
            FuncInsert(iOrbM2, eVal, eElt);
          od;
        od;
        if First(ListCompleteValue, x->x<>0)<>fail then
          Error("Apparently, the boundary does not squares to zero");
        fi;
      fi;
    od;
  od;
end;


CheckCollapsingPolyhedralTesselation:=function(TheBound)
  local len, i, nbC, eEnt, ListRec, iC, len2, i2, iFace, eSign, eElt, eEntB, len3, i3, iFaceB, eSignB, eEltB, eProd, TheStab, TheRot, TheRecInfo, nbCos, iCos, SumVal, lenR, iR, eVal;
  len:=Length(TheBound.ListOrbitByRank);
  for i in [4..len]
  do
    nbC:=Length(TheBound.ListOrbitByRank[i-2]);
    for eEnt in TheBound.ListOrbitByRank[i]
    do
      ListRec:=[];
      for iC in [1..nbC]
      do
        Add(ListRec, rec(ListVal:=[], ListElt:=[]));
      od;
      len2:=Length(eEnt.BoundaryImage.ListIFace);
      for i2 in [1..len2]
      do
        iFace:=eEnt.BoundaryImage.ListIFace[i2];
        eSign:=eEnt.BoundaryImage.ListSign[i2];
        eElt:=eEnt.BoundaryImage.ListElt[i2];
        eEntB:=TheBound.ListOrbitByRank[i-1][iFace];
        len3:=Length(eEntB.BoundaryImage.ListIFace);
        for i3 in [1..len3]
        do
          iFaceB:=eEntB.BoundaryImage.ListIFace[i3];
          eSignB:=eEntB.BoundaryImage.ListSign[i3];
          eEltB:=eEntB.BoundaryImage.ListElt[i3];
          eProd:=eEltB*eElt;
          Add(ListRec[iFaceB].ListVal, eSign*eSignB);
          Add(ListRec[iFaceB].ListElt, eProd);
        od;
      od;
      for iC in [1..nbC]
      do
        TheStab:=TheBound.ListOrbitByRank[i-2][iC].TheStab;
        TheRot:=TheBound.ListOrbitByRank[i-2][iC].RotationSubgroup;
        TheRecInfo:=RightCosetExpression(TheStab, ListRec[iC]);
        nbCos:=Length(TheRecInfo);
        for iCos in [1..nbCos]
        do
          SumVal:=0;
          lenR:=Length(TheRecInfo[iCos].ListVal);
          for iR in [1..lenR]
          do
            eVal:=TheRecInfo[iCos].ListVal[iR];
            eElt:=TheRecInfo[iCos].ListElt[iR];
            if eElt in TheRot then
              eSign:=1;
            else
              eSign:=-1;
            fi;
            SumVal:=SumVal + eSign*eVal;
          od;
          if SumVal<>0 then
            Error("We fail collapsing property");
          fi;
        od;
      od;
    od;
  od;
end;

DoDualizationDirectTranspose:=function(TheBound)
  local len, ListListStab, i, ListStab, eOrbit, ListOrbitByRankDual, nbOrbitSource, nbOrbitTarget, iOrbitSource, NewFuncSignatureDet, iOrbitTarget, ListRecordBoundary, pos, eElt, eNewSign, eCos, eRepr, iFaceSource, TheStabSource, TheInt, ListCoset, TheIndStab, TheSet, eSign, TheStabTarget, TheRec, TheLen, iVal, eEltInv, eEltDet, NewListAdd, iEnt, nbEnt, eSet, FuncSignatureDet, ListListRot, ListRot, eStab, eRotSub, ListMatrGens, ListSignGens, ePerm, eGen, GRPsym, eRotSubgroup, IsOrientable;
  FuncSignatureDet:=function(iRank, iFace, eElt)
    if not(eElt in TheBound.ListOrbitByRank[iRank+2][iFace].TheStab) then
      Error("The element is not in the Stabilizer");
    fi;
    if eElt in TheBound.ListOrbitByRank[iRank+2][iFace].RotationSubgroup then
      return 1;
    fi;
    return -1;
  end;
  len:=Length(TheBound.ListOrbitByRank);
  ListListStab:=[];
  ListListRot:=[];
  for i in [2..len]
  do
    ListStab:=[];
    for eOrbit in TheBound.ListOrbitByRank[i]
    do
      Add(ListStab, eOrbit.TheStab);
    od;
    Add(ListListStab, ListStab);
    ListRot:=[];
    for eOrbit in TheBound.ListOrbitByRank[i]
    do
      Add(ListRot, eOrbit.RotationSubgroup);
    od;
    Add(ListListRot, ListRot);
  od;
  ListOrbitByRankDual:=[];
  NewFuncSignatureDet:=function(iRank, iFace, eElt)
    return TheBound.FuncSignatureDet(iRank, iFace, eElt)*TheBound.FuncDeterminant(eElt);
  end;
  for i in [2..len-1]
  do
    Print("i=", i, "\n");
    nbOrbitSource:=Length(TheBound.ListOrbitByRank[i]);
    nbOrbitTarget:=Length(TheBound.ListOrbitByRank[i+1]);
    ListRecordBoundary:=[];
    for iOrbitSource in [1..nbOrbitSource]
    do
      Add(ListRecordBoundary, rec(ListIFace:=[], ListSign:=[], ListElt:=[]));
    od;
    for iOrbitTarget in [1..nbOrbitTarget]
    do
      TheRec:=TheBound.ListOrbitByRank[i+1][iOrbitTarget];
      TheStabTarget:=TheRec.TheStab;
      TheSet:=Set(TheRec.BoundaryImage.ListOriginCells);
      nbEnt:=Length(TheSet);
#      Print("  iOrbitTarget=", iOrbitTarget, "/", nbOrbitTarget, " |TheStabTarget|=", Order(TheStabTarget), "\n");
      for iEnt in [1..nbEnt]
      do
        iVal:=TheSet[iEnt];
        eSet:=Filtered(TheRec.BoundaryImage.ListOriginCells, x->x=iVal);
        Print("    iEnt=", iEnt, "/", nbEnt, " |siz|=", Length(eSet), "\n");
        pos:=Position(TheSet, iVal);
        eElt:=TheRec.BoundaryImage.ListElt[pos];
        eSign:=TheRec.BoundaryImage.ListSign[pos];
        iFaceSource:=TheRec.BoundaryImage.ListIFace[pos];
        TheIndStab:=ConjugateGroup(TheStabTarget, eElt);
#        Print("    eElt=", eElt, "\n");
        TheStabSource:=TheBound.ListOrbitByRank[i][iFaceSource].TheStab;
        TheInt:=Intersection(TheIndStab, TheStabSource);
#        Print("    |TheStabSource|=", Order(TheStabSource), " |TheIndStab|=", Order(TheIndStab), " |TheInt|=", Order(TheInt), "\n");
        ListCoset:=RightCosets(TheStabSource, TheInt);
        eEltInv:=Inverse(eElt);
        eEltDet:=TheBound.FuncDeterminant(eElt);
        for eCos in ListCoset
        do
          eRepr:=Representative(eCos);
          Add(ListRecordBoundary[iFaceSource].ListElt, eEltInv*Inverse(eRepr));
          Add(ListRecordBoundary[iFaceSource].ListIFace, iOrbitTarget);
          eNewSign:=eSign*eEltDet*TheBound.FuncDeterminant(eRepr)*FuncSignatureDet(i-2, iFaceSource, eRepr);
          Add(ListRecordBoundary[iFaceSource].ListSign, eNewSign);
        od;
      od;
    od;
    NewListAdd:=[];
    for iOrbitSource in [1..nbOrbitSource]
    do
      eStab:=ListListStab[i-1][iOrbitSource];
      eRotSub:=ListListRot[i-1][iOrbitSource];
      ListMatrGens:=GeneratorsOfGroup(eStab);
      ListSignGens:=[];
      IsOrientable:=true;
      for eGen in ListMatrGens
      do
        if eGen in eRotSub then
          eSign:= TheBound.FuncDeterminant(eGen);
        else
          eSign:=-TheBound.FuncDeterminant(eGen);
        fi;
        if eSign=1 then
          ePerm:=();
        else
          ePerm:=(1,2);
          IsOrientable:=false;
        fi;
        Add(ListSignGens, ePerm);
      od;
      GRPsym:=Group([(1,2)]);
      eRotSubgroup:=GetKernelOfMapping(eStab, GRPsym, ListMatrGens, ListSignGens);
      Add(NewListAdd, rec(TheStab:=eStab, 
                          BoundaryImage:=ListRecordBoundary[iOrbitSource],
                          IsOrientable:=IsOrientable, 
                          RotationSubgroup:=eRotSubgroup));
    od;
    Add(ListOrbitByRankDual, NewListAdd);
  od;
  NewListAdd:=[];
  for iOrbitTarget in [1..nbOrbitTarget]
  do
    Add(NewListAdd, rec(TheStab:=ListListStab[i][iOrbitTarget]));
  od;
  Add(ListOrbitByRankDual, NewListAdd);
  return rec(ListOrbitByRank:=ListOrbitByRankDual, 
             FuncDeterminant:=TheBound.FuncDeterminant);
end;


CheckHomologyVanishingBoundaries:=function(TheBound)
  local RelDim, len, i, TheDim, TheDimB, ListRecSums, j, FuncInsert, eSign, eElt, iFace, len2, j2, eSign2, eElt2, iFace2, eSignIns, jIns, eEltIns, iOrb;
  RelDim:=Length(TheBound.ListOrbitByRank)-4;
  for i in [2..RelDim]
  do
    Print("  i=", i, " step 1\n");
    TheDim:=Length(TheBound.ListOrbitByRank[i+2]);
    TheDimB:=Length(TheBound.ListOrbitByRank[i]);
    ListRecSums:=[];
    for j in [1..TheDimB]
    do
      Add(ListRecSums, rec(ListSums:=[], ListElt:=[]));
    od;
    FuncInsert:=function(eElt, eSign, j)
      local nbEnt, eStab, eRot, iEnt, eQuot, eSignInc;
      eStab:=TheBound.ListOrbitByRank[i][j].TheStab;
      eRot :=TheBound.ListOrbitByRank[i][j].RotationSubgroup;
      nbEnt:=Length(ListRecSums[j].ListElt);
      for iEnt in [1..nbEnt]
      do
        eQuot:=eElt*Inverse(ListRecSums[j].ListElt[iEnt]);
        if eQuot in eStab then
          if eQuot in eRot then
            eSignInc:=1;
          else
            eSignInc:=-1;
          fi;
          ListRecSums[j].ListSums[iEnt]:=ListRecSums[j].ListSums[iEnt] + eSign*eSignInc;
          return;
        fi;
      od;
      Add(ListRecSums[j].ListSums, eSign);
      Add(ListRecSums[j].ListElt, eElt);
    end;
    Print("  i=", i, " step 2\n");
    for iOrb in [1..TheDim]
    do
      len:=Length(TheBound.ListOrbitByRank[i+2][iOrb].BoundaryImage.ListSign);
      for j in [1..len]
      do
        eSign:=TheBound.ListOrbitByRank[i+2][iOrb].BoundaryImage.ListSign[j];
        eElt:=TheBound.ListOrbitByRank[i+2][iOrb].BoundaryImage.ListElt[j];
        iFace:=TheBound.ListOrbitByRank[i+2][iOrb].BoundaryImage.ListIFace[j];
        len2:=Length(TheBound.ListOrbitByRank[i+1][iFace].BoundaryImage.ListSign);
        for j2 in [1..len2]
        do
          eSign2:=TheBound.ListOrbitByRank[i+1][iFace].BoundaryImage.ListSign[j2];
          eElt2:=TheBound.ListOrbitByRank[i+1][iFace].BoundaryImage.ListElt[j2];
          iFace2:=TheBound.ListOrbitByRank[i+1][iFace].BoundaryImage.ListIFace[j2];
          eSignIns:=eSign*eSign2;
          jIns:=iFace2;
          eEltIns:=eElt2*eElt;
          FuncInsert(eEltIns, eSignIns, jIns);
        od;
      od;
    od;
    Print("  i=", i, " step 3\n");
    for j in [1..TheDimB]
    do
      if First(ListRecSums[j].ListSums, x->x<>0)<>fail then
        Error("Non vanishing of some product");
      fi;
    od;
    Print("  i=", i, " step 4\n");
  od;
  Print("We pass G-module square vanishing test\n");
end;


CheckCohomologyVanishingBoundaries:=function(TheBound)
  local RelDim, len, i, TheDim, TheDimB, ListRecSums, j, FuncInsert, eSign, eElt, iFace, len2, j2, eSign2, eElt2, iFace2, eSignIns, jIns, eEltIns, iOrb;
  RelDim:=Length(TheBound.ListOrbitByRank)-3;
  Print("Beginning of CheckCohomologyVanishingBoundaries\n");
  for i in [0..RelDim]
  do
    TheDim:=Length(TheBound.ListOrbitByRank[i+1]);
    TheDimB:=Length(TheBound.ListOrbitByRank[i+3]);
    for iOrb in [1..TheDim]
    do
      ListRecSums:=[];
      for j in [1..TheDimB]
      do
        Add(ListRecSums, rec(ListSums:=[], ListAbsSums:=[], ListElt:=[]));
      od;
      FuncInsert:=function(eElt, eSign, j)
        local nbEnt, eStab, eRot, iEnt, eQuot, eSignInc;
        eStab:=TheBound.ListOrbitByRank[i+3][j].TheStab;
        eRot :=TheBound.ListOrbitByRank[i+3][j].RotationSubgroup;
        nbEnt:=Length(ListRecSums[j].ListElt);
        for iEnt in [1..nbEnt]
        do
          eQuot:=eElt*Inverse(ListRecSums[j].ListElt[iEnt]);
          if eQuot in eStab then
            if eQuot in eRot then
              eSignInc:=1;
            else
              eSignInc:=-1;
            fi;
            ListRecSums[j].ListSums[iEnt]:=ListRecSums[j].ListSums[iEnt] + eSign*eSignInc;
            ListRecSums[j].ListAbsSums[iEnt]:=ListRecSums[j].ListAbsSums[iEnt] + 1;
            return;
          fi;
        od;
        Add(ListRecSums[j].ListSums, eSign);
        Add(ListRecSums[j].ListAbsSums, 1);
        Add(ListRecSums[j].ListElt, eElt);
      end;
      len:=Length(TheBound.ListOrbitByRank[i+1][iOrb].BoundaryImage.ListSign);
      for j in [1..len]
      do
        eSign:=TheBound.ListOrbitByRank[i+1][iOrb].BoundaryImage.ListSign[j];
        eElt:=TheBound.ListOrbitByRank[i+1][iOrb].BoundaryImage.ListElt[j];
        iFace:=TheBound.ListOrbitByRank[i+1][iOrb].BoundaryImage.ListIFace[j];
        len2:=Length(TheBound.ListOrbitByRank[i+2][iFace].BoundaryImage.ListSign);
        for j2 in [1..len2]
        do
          eSign2:=TheBound.ListOrbitByRank[i+2][iFace].BoundaryImage.ListSign[j2];
          eElt2:=TheBound.ListOrbitByRank[i+2][iFace].BoundaryImage.ListElt[j2];
          iFace2:=TheBound.ListOrbitByRank[i+2][iFace].BoundaryImage.ListIFace[j2];
          eSignIns:=eSign*eSign2;
          jIns:=iFace2;
          eEltIns:=eElt2*eElt;
          FuncInsert(eEltIns, eSignIns, jIns);
        od;
      od;
      for j in [1..TheDimB]
      do
        if First(ListRecSums[j].ListAbsSums, x->x<>2)<>fail then
          Error("Number of entries different from 2");
        fi;
        if First(ListRecSums[j].ListSums, x->x<>0)<>fail then
          Error("Non vanishing of some product");
        fi;
      od;
    od;
  od;
  Print("Ending of CheckCohomologyVanishingBoundaries\n");
end;




BredonHomologyFromTesselation:=function(TheBoundDual)
  local ListRepresentationRings, nbRank, iRank, ListIrr, eRec, ListListDim, ListListBegin, ListListEnd, ListDim, ListBegin, ListEnd, ListTotalDim, ListMatrix, eMatrix, eBegin, eEnd, pos1, pos2, r, RelStab, RelReprRing, irrH, TheM, DblPerm, TheIrr, TheH, eElt, iFaceM1, iEnt, eOrbit, fBegin, fEnd, eSign, iOrbit, CanStab, BoundSiz, eDim, nbOrbit, pos, nbRep, iCol, test, TheReprRing;
  ListRepresentationRings:=[];
  ListListDim:=[];
  ListListBegin:=[];
  ListListEnd:=[];
  nbRank:=Length(TheBoundDual.ListOrbitByRankDual);
  ListTotalDim:=[];
  for iRank in [1..nbRank]
  do
    ListIrr:=[];
    ListDim:=[];
    ListBegin:=[];
    ListEnd:=[];
    pos:=0;
    for eRec in TheBoundDual.ListOrbitByRankDual[iRank]
    do
      TheIrr:=Irr(eRec.TheStab);
      nbRep:=Length(TheIrr);
      Add(ListIrr, TheIrr);
      Add(ListDim, nbRep);
      Add(ListBegin, pos+1);
      Add(ListEnd, pos+nbRep);
      pos:=pos+nbRep;
    od;
    Add(ListRepresentationRings, ListIrr);
    Add(ListListDim, ListDim);
    Add(ListListBegin, ListBegin);
    Add(ListListEnd, ListEnd);
    Add(ListTotalDim, pos);
  od;
  ListMatrix:=[];
  for iRank in [1..nbRank-1]
  do
    Print("iRank=", iRank, "/", nbRank, "\n");
    eMatrix:=NullMat(ListTotalDim[iRank], ListTotalDim[iRank+1]);
    nbOrbit:=Length(TheBoundDual.ListOrbitByRankDual[iRank]);
    for iOrbit in [1..nbOrbit]
    do
      Print("  iOrbit=", iOrbit, "/", nbOrbit, "\n");
      eOrbit:=TheBoundDual.ListOrbitByRankDual[iRank][iOrbit];
      eBegin:=ListListBegin[iRank][iOrbit];
      eEnd:=ListListEnd[iRank][iOrbit];
      BoundSiz:=Length(eOrbit.BoundaryImage.ListIFace);
      CanStab:=TheBoundDual.ListOrbitByRankDual[iRank][iOrbit].TheStab;
      TheReprRing:=ListRepresentationRings[iRank][iOrbit];
      for iEnt in [1..BoundSiz]
      do
        iFaceM1:=eOrbit.BoundaryImage.ListIFace[iEnt];
        eSign:=eOrbit.BoundaryImage.ListSign[iEnt];
        eElt:=eOrbit.BoundaryImage.ListElt[iEnt];
        fBegin:=ListListBegin[iRank+1][iFaceM1];
        fEnd:=ListListEnd[iRank+1][iFaceM1];
        RelStab:=TheBoundDual.ListOrbitByRankDual[iRank+1][iFaceM1].TheStab;
        RelReprRing:=ListRepresentationRings[iRank+1][iFaceM1];
        TheH:=ConjugateGroup(CanStab, Inverse(eElt));
        test:=IsSubgroup(RelStab, TheH);
        Print(" |CanStab|=", Order(CanStab), " |RelStab|=", Order(RelStab), " test=", test, "\n");
        if test=false then
          Error("Please debug from here");
        fi;
        TheIrr:=Irr(TheH);
        DblPerm:=TransformingPermutations(TheIrr, TheReprRing);
        irrH:=Permuted(List(TheIrr, x->Permuted(x, DblPerm.columns)), DblPerm.rows);
        TheM:=MatScalarProducts(RelReprRing, InducedClassFunctions(irrH, RelStab));
        pos1:=0;
        for r in [eBegin..eEnd]
        do
          pos1:=pos1+1;
          pos2:=0;
          for iCol in [fBegin..fEnd]
          do
            pos2:=pos2+1;
            eMatrix[r][iCol]:=eSign*TheM[pos1][pos2];
          od;
        od;
      od;
    od;
    Add(ListMatrix, eMatrix);
  od;
  return ListMatrix;
end;


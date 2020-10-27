GMOD_GetZero:=function()
  return rec(ListVal:=[], ListElt:=[]);
end;

GMOD_GetZeroVector:=function(n)
  local ListReturn, i;
  ListReturn:=[];
  for i in [1..n]
  do
    Add(ListReturn, rec(ListVal:=[], ListElt:=[]));
  od;
  return ListReturn;
end;
GMOD_GetZeroMatrix:=function(nbLine,nbCol)
  local TheMat;
  TheMat:=List([1..nbLine], x->GMOD_GetZeroVector(nbCol));
  return rec(nbLine:=nbLine, nbCol:=nbCol, TheMat:=TheMat);
end;


GmoduleMultiplication:=function(GM1, GM2)
  local ListNewVals, ListNewElts, FuncInsert, nbR1, nbR2, iR1, iR2, eSet;
  ListNewVals:=[];
  ListNewElts:=[];
  FuncInsert:=function(eVal, eElt)
    local pos;
    pos:=Position(ListNewElts, eElt);
    if pos=fail then
      Add(ListNewVals, eVal);
      Add(ListNewElts, eElt);
    else
      ListNewVals[pos]:=ListNewVals[pos]+eVal;
    fi;
  end;
  nbR1:=Length(GM1.ListVal);
  nbR2:=Length(GM2.ListVal);
  for iR1 in [1..nbR1]
  do
    for iR2 in [1..nbR2]
    do
      FuncInsert(GM1.ListVal[iR1]*GM2.ListVal[iR2], GM1.ListElt[iR1]*GM2.ListElt[iR2]);
    od;
  od;
  eSet:=Filtered([1..Length(ListNewVals)], x->ListNewVals[x]<>0);
  return rec(ListVal:=ListNewVals{eSet}, ListElt:=ListNewElts{eSet});
end;


GmoduleAddition:=function(GM1, GM2)
  local ListNewVals, ListNewElts, FuncInsert, nbR1, nbR2, iR1, iR2, eSet;
  ListNewVals:=StructuralCopy(GM1.ListVal);
  ListNewElts:=StructuralCopy(GM1.ListElt);
  FuncInsert:=function(eVal, eElt)
    local pos;
    pos:=Position(ListNewElts, eElt);
    if pos=fail then
      Add(ListNewVals, eVal);
      Add(ListNewElts, eElt);
    else
      ListNewVals[pos]:=ListNewVals[pos]+eVal;
    fi;
  end;
  nbR2:=Length(GM2.ListVal);
  for iR2 in [1..nbR2]
  do
    FuncInsert(GM2.ListVal[iR2], GM2.ListElt[iR2]);
  od;
  eSet:=Filtered([1..Length(ListNewVals)], x->ListNewVals[x]<>0);
  return rec(ListVal:=ListNewVals{eSet}, ListElt:=ListNewElts{eSet});
end;

# returns GM1 - GM2
GmoduleSoustraction:=function(GM1, GM2)
  local ListNewVals, ListNewElts, FuncInsert, nbR1, nbR2, iR1, iR2, eSet;
  ListNewVals:=StructuralCopy(GM1.ListVal);
  ListNewElts:=StructuralCopy(GM1.ListElt);
  FuncInsert:=function(eVal, eElt)
    local pos;
    pos:=Position(ListNewElts, eElt);
    if pos=fail then
      Add(ListNewVals, eVal);
      Add(ListNewElts, eElt);
    else
      ListNewVals[pos]:=ListNewVals[pos]+eVal;
    fi;
  end;
  nbR2:=Length(GM2.ListVal);
  for iR2 in [1..nbR2]
  do
    FuncInsert(-GM2.ListVal[iR2], GM2.ListElt[iR2]);
  od;
  eSet:=Filtered([1..Length(ListNewVals)], x->ListNewVals[x]<>0);
  return rec(ListVal:=ListNewVals{eSet}, ListElt:=ListNewElts{eSet});
end;

VectorGmoduleSoustraction:=function(vectGM1, vectGM2)
  local TheLen;
  TheLen:=Length(vectGM1);
  return List([1..TheLen], x->GmoduleSoustraction(vectGM1[x], vectGM2[x]));
end;


MatrixGmoduleTranspose:=function(TheMat)
  return rec(nbLine:=TheMat.nbCol, nbCol:=TheMat.nbLine, TheMat:=TransposedMat(TheMat.TheMat));
end;


VectorMatrixGmoduleMultiplication:=function(eVect1, TheMat2)
  local nbCol1, nbLine2, nbCol2, eLine, iCol, TheVal, idx, TheProd;
  nbCol1:=Length(eVect1);
  nbLine2:=TheMat2.nbLine;
  if nbCol1<>nbLine2 then
    Print("Inconsistency in matrix multiplication\n");
    Print("eVect1 : nbCol1=", nbCol1, " TheMat2, nbLine2=", nbLine2, "\n");
    Error("Please correct your call");
  fi;
  nbCol2:=TheMat2.nbCol;
  eLine:=[];
  for iCol in [1..nbCol2]
  do
    TheVal:=rec(ListVal:=[], ListElt:=[]);
    for idx in [1..nbCol1]
    do
#   I know it is strange but that is how it should be:
      TheProd:=GmoduleMultiplication(TheMat2.TheMat[idx][iCol], eVect1[idx]);
      TheVal:=GmoduleAddition(TheVal, TheProd);
    od;
    Add(eLine, TheVal);
  od;
  return eLine;
end;

MatrixMatrixGmoduleMultiplication:=function(TheMat1, TheMat2)
  return rec(nbLine:=TheMat1.nbLine, nbCol:=TheMat2.nbCol, TheMat:=List(TheMat1.TheMat, x->VectorMatrixGmoduleMultiplication(x, TheMat2)));
end;


GMOD_IsItGmoduleVector:=function(TheVect, TheGRP)
  local eRec, eEnt;
  for eRec in TheVect
  do
    for eEnt in eRec.ListElt
    do
      if not(eEnt in TheGRP) then
        return false;
      fi;
    od;
  od;
  return true;
end;


VectorGmoduleAddition:=function(TheVect1, TheVect2)
  local TheRet, iCol;
  TheRet:=[];
  for iCol in [1..Length(TheVect1)]
  do
    Add(TheRet, GmoduleAddition(TheVect1[iCol], TheVect2[iCol]));
  od;
  return TheRet;
end;


MatrixGmoduleAddition:=function(TheMat1, TheMat2)
  local nbLine1, nbCol1, nbLine2, nbCol2, NewMat, iLine, eLine, iCol;
  nbLine1:=TheMat1.nbLine;
  nbCol1:=TheMat1.nbCol;
  nbLine2:=TheMat2.nbLine;
  nbCol2:=TheMat2.nbCol;
  if nbLine1<>nbLine2 or nbCol1<>nbCol2 then
    Error("Dimension error in matrix addition");
  fi;
  NewMat:=[];
  for iLine in [1..nbLine1]
  do
    eLine:=[];
    for iCol in [1..nbCol1]
    do
      Add(eLine, GmoduleAddition(TheMat1.TheMat[iLine][iCol], TheMat2.TheMat[iLine][iCol]));
    od;
    Add(NewMat, eLine);
  od;
  return rec(nbLine:=nbLine1, nbCol:=nbCol1, TheMat:=NewMat);
end;


GMOD_MatrixTwisting:=function(TheMatrix, FctSign)
  local nbLine, nbCol, NewMat, iLine, eLine, iCol, eEnt, nbC, ListVal, iC, eSign;
  nbLine:=TheMatrix.nbLine;
  nbCol:=TheMatrix.nbCol;
  NewMat:=[];
  for iLine in [1..nbLine]
  do
    eLine:=[];
    for iCol in [1..nbCol]
    do
      eEnt:=TheMatrix.TheMat[iLine][iCol];
      nbC:=Length(eEnt.ListElt);
      ListVal:=[];
      for iC in [1..nbC]
      do
        eSign:=eEnt.ListVal[iC]*FctSign(eEnt.ListElt[iC]);
        Add(ListVal, eSign);
      od;
      Add(eLine, rec(ListVal:=ListVal, ListElt:=eEnt.ListElt));
    od;
    Add(NewMat, eLine);
  od;
  return rec(nbLine:=nbLine, nbCol:=nbCol, TheMat:=NewMat);
end;


MatrixGmoduleOpposite:=function(TheMat)
  local nbLine, nbCol, NewMat, iLine, eLine, iCol;
  nbLine:=TheMat.nbLine;
  nbCol:=TheMat.nbCol;
  NewMat:=[];
  for iLine in [1..nbLine]
  do
    eLine:=[];
    for iCol in [1..nbCol]
    do
      Add(eLine, rec(ListVal:=-TheMat.TheMat[iLine][iCol].ListVal, ListElt:=TheMat.TheMat[iLine][iCol].ListElt));
    od;
    Add(NewMat, eLine);
  od;
  return rec(nbLine:=nbLine, nbCol:=nbCol, TheMat:=NewMat);
end;
VectorGmoduleOpposite:=function(TheVector)
  local eLine, iCol;
  eLine:=[];
  for iCol in [1..Length(TheVector)]
  do
    Add(eLine, rec(ListVal:=-TheVector[iCol].ListVal, ListElt:=TheVector[iCol].ListElt));
  od;
  return eLine;
end;


IsZeroReducedGmoduleElt:=function(eElt)
  return Length(eElt.ListVal)=0;
end;
IsZeroReducedGmoduleVector:=function(TheVect)
  local eCol, test;
  for eCol in TheVect
  do
    test:=IsZeroReducedGmoduleElt(eCol);
    if test=false then
      return false;
    fi;
  od;
  return true;
end;
IsZeroReducedGmoduleMatrix:=function(TheMat)
  local eLine, test;
  for eLine in TheMat.TheMat
  do
    test:=IsZeroReducedGmoduleVector(eLine);
    if test=false then
      return false;
    fi;
  od;
  return true;
end;



IsEqualReducedGmoduleElt:=function(TheRec1, TheRec2)
  local ListElt1, ListElt2, eElt, pos1, pos2;
  ListElt1:=TheRec1.ListElt;
  ListElt2:=TheRec2.ListElt;
  if Set(ListElt1)<>Set(ListElt2) then
    return false;
  fi;
  for eElt in ListElt1
  do
    pos1:=Position(ListElt1, eElt);
    pos2:=Position(ListElt2, eElt);
    if TheRec1.ListVal[pos1]<>TheRec2.ListVal[pos2] then
      return false;
    fi;
  od;
  return true;
end;

IsEqualReducedGmoduleVector:=function(TheVect1, TheVect2)
  local iCol;
  if Length(TheVect1)<>Length(TheVect2) then
    return false;
  fi;
  for iCol in [1..Length(TheVect1)]
  do
    if IsEqualReducedGmoduleElt(TheVect1[iCol], TheVect2[iCol])=false then
      return false;
    fi;
  od;
  return true;
end;

IsEqualReducedGmoduleMatrix:=function(TheMat1, TheMat2)
  local iLine;
  if TheMat1.nbLine<>TheMat2.nbLine then
    return false;
  fi;
  for iLine in [1..TheMat1.nbLine]
  do
    if IsEqualReducedGmoduleVector(TheMat1.TheMat[iLine], TheMat2.TheMat[iLine])=false then
      return false;
    fi;
  od;
  return true;
end;



ReducedGmoduleForm:=function(TheRec)
  local SetElt, NewListVal, NewListElt, eElt, HC, TheSum;
  SetElt:=Set(TheRec.ListElt);
  NewListVal:=[];
  NewListElt:=[];
  for eElt in SetElt
  do
    HC:=Filtered([1..Length(TheRec.ListElt)], x->TheRec.ListElt[x]=eElt);
    TheSum:=Sum(TheRec.ListVal{HC});
    if TheSum<>0 then
      Add(NewListVal, TheSum);
      Add(NewListElt, eElt);
    fi;
  od;
  return rec(ListVal:=NewListVal, ListElt:=NewListElt);
end;
ReducedGmoduleVector:=function(TheVect)
  return List(TheVect, ReducedGmoduleForm);
end;
ReducedGmoduleMatrix:=function(TheMat)
  return rec(nbLine:=TheMat.nbLine, nbCol:=TheMat.nbCol, TheMat:=List(TheMat.TheMat, ReducedGmoduleVector));
end;

IsZeroGmoduleElt:=function(eElt)
  return IsZeroReducedGmoduleElt(ReducedGmoduleForm(eElt));
end;
IsZeroGmoduleVector:=function(TheVect)
  return IsZeroReducedGmoduleVector(ReducedGmoduleVector(TheVect));
end;
IsZeroGmoduleMatrix:=function(TheMat)
  return IsZeroReducedGmoduleMatrix(ReducedGmoduleMatrix(TheMat));
end;



IsEqualGmoduleVector:=function(TheVect1, TheVect2)
  return IsEqualReducedGmoduleVector(ReducedGmoduleVector(TheVect1), ReducedGmoduleVector(TheVect2));
end;
IsEqualGmoduleMatrix:=function(TheMat1, TheMat2)
  return IsEqualReducedGmoduleMatrix(ReducedGmoduleMatrix(TheMat1), ReducedGmoduleMatrix(TheMat2));
end;


RightCosetExpression:=function(TheStab, TheElt)
  local ListRightCoset, FuncInsertValue, iVal;
  ListRightCoset:=[];
  FuncInsertValue:=function(eVal, eElt)
    local iCos, eQuot, TheVect;
    for iCos in [1..Length(ListRightCoset)]
    do
      eQuot:=eElt*ListRightCoset[iCos].eCos^(-1);
      if eQuot in TheStab then
        Add(ListRightCoset[iCos].ListVal, eVal);
        Add(ListRightCoset[iCos].ListElt, eQuot);
        return;
      fi;
    od;
    Add(ListRightCoset, rec(eCos:=eElt, ListVal:=[eVal], ListElt:=[Identity(TheStab)]));
  end;
  for iVal in [1..Length(TheElt.ListElt)]
  do
    FuncInsertValue(TheElt.ListVal[iVal], TheElt.ListElt[iVal]);
  od;
  return ListRightCoset;
end;


RightCosetVectorExpression:=function(TheStab, eVectSel)
  local ListRightCoset, TheDimInput, FuncInsertValue, iCol, iVal;
  ListRightCoset:=[];
  TheDimInput:=Length(eVectSel);
  FuncInsertValue:=function(eVal, iCol, eElt)
    local iCos, eQuot, TheVect;
    for iCos in [1..Length(ListRightCoset)]
    do
      eQuot:=eElt*ListRightCoset[iCos].eCos^(-1);
      if eQuot in TheStab then
        Add(ListRightCoset[iCos].TheVect[iCol].ListVal, eVal);
        Add(ListRightCoset[iCos].TheVect[iCol].ListElt, eQuot);
        return;
      fi;
    od;
    TheVect:=GMOD_GetZeroVector(TheDimInput);
    Add(TheVect[iCol].ListVal, eVal);
    Add(TheVect[iCol].ListElt, Identity(TheStab));
    Add(ListRightCoset, rec(eCos:=eElt, TheVect:=TheVect));
  end;
  for iCol in [1..TheDimInput]
  do
    for iVal in [1..Length(eVectSel[iCol].ListElt)]
    do
      FuncInsertValue(eVectSel[iCol].ListVal[iVal], iCol, eVectSel[iCol].ListElt[iVal]);
    od;
  od;
  return ListRightCoset;
end;


# we solve the equation TheElt = x * TheMulti
# with all elements in a G module
GMOD_SolutionMultiplication:=function(TheElt, TheMulti, TheGroup)
  local ListElement, eElt, nbElt, ListEqua, TheVect, nbEnt, iEnt, eProd, pos, TheB, eSol, TheReturn;
  # Curiously, if we use Elements(TheGroup)
  # then we get some big bad errors in the solutioning
  ListElement:=[];
  for eElt in TheGroup
  do
    Add(ListElement, eElt);
  od;
  nbElt:=Length(ListElement);
  ListEqua:=[];
  for eElt in TheGroup
  do
    TheVect:=ListWithIdenticalEntries(nbElt,0);
    nbEnt:=Length(TheMulti.ListVal);
    for iEnt in [1..nbEnt]
    do
      eProd:=eElt*TheMulti.ListElt[iEnt];
      pos:=Position(ListElement, eProd);
      TheVect[pos]:=TheMulti.ListVal[iEnt];
    od;
    Add(ListEqua, TheVect);
  od;
  TheB:=ListWithIdenticalEntries(nbElt,0);
  nbEnt:=Length(TheElt.ListVal);
  for iEnt in [1..nbEnt]
  do
    pos:=Position(ListElement, TheElt.ListElt[iEnt]);
    TheB[pos]:=TheElt.ListVal[iEnt];
  od;
  eSol:=SolutionIntMat(ListEqua, TheB);
  if eSol=fail then
    Error("No solution to your equation");
  fi;
  TheReturn:=ReducedGmoduleForm(rec(ListVal:=eSol, ListElt:=ListElement));
  if IsEqualReducedGmoduleElt(TheElt, GmoduleMultiplication(TheReturn, TheMulti))=false then
    Error("GMOD_SolutionMultiplication was not correct");
  fi;
  return TheReturn;
end;



GMOD_SolutionMatrixMultiplication:=function(TheVect, TheMatrix, TheGroup)
  local nbLine, eElt, nbCol, ListElement, nbElt, GetVector, ListEqua, iLine, iElt, iIdent, TheB, TheSol, TheReturn, pos, ListVal, ListElt;
  nbLine:=TheMatrix.nbLine;
  nbCol:=TheMatrix.nbCol;
  ListElement:=[];
  for eElt in TheGroup
  do
    Add(ListElement, eElt);
  od;
  nbElt:=Length(ListElement);
  GetVector:=function(TheVect, iElt)
    local eVect, TheOff, iCol, eEnt, len, i, eVal, eElt, pos;
    eVect:=ListWithIdenticalEntries(nbCol*nbElt, 0);
    TheOff:=0;
    for iCol in [1..nbCol]
    do
      eEnt:=TheVect[iCol];
      len:=Length(eEnt.ListVal);
      for i in [1..len]
      do
        eVal:=eEnt.ListVal[i];
        eElt:=eEnt.ListElt[i]*ListElement[iElt];
        pos:=Position(ListElement, eElt);
        eVect[TheOff+pos]:=eVal;
      od;
      TheOff:=TheOff+nbElt;
    od;
    return eVect;
  end;
  ListEqua:=[];
  for iLine in [1..nbLine]
  do
    for iElt in [1..nbElt]
    do
      Add(ListEqua, GetVector(TheMatrix.TheMat[iLine], iElt));
    od;
  od;
  iIdent:=Position(ListElement, ());
  TheB:=GetVector(TheVect, iIdent);
  TheSol:=SolutionIntMat(ListEqua, TheB);
  if TheSol=fail then
    Error("The Equation has no solution");
  fi;
  TheReturn:=[];
  pos:=0;
  for iLine in [1..nbLine]
  do
    ListVal:=[];
    ListElt:=[];
    for iElt in [1..nbElt]
    do
      pos:=pos+1;
      if TheSol[pos]<>0 then
        Add(ListVal, TheSol[pos]);
        Add(ListElt, ListElement[iElt]);
      fi;
    od;
    Add(TheReturn, rec(ListVal:=ListVal, ListElt:=ListElt));
  od;
  return TheReturn;
end;


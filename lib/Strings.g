
StringNumberGeneric:=function(nb, len, eStrEmpty)
  local idx, TheStr, U;
  if nb > 10^(len)-1 then
    Error("the number is greater than the allowed size");
  fi;
  idx:=1;
  while(true)
  do
    if nb < 10^(idx) then
      TheStr:="";
      for U in [1..len-idx]
      do
        TheStr:=Concatenation(TheStr, eStrEmpty);
      od;
      return Concatenation(TheStr, String(nb));
    fi;
    idx:=idx+1;
  od;
end;

StringNumber:=function(nb, len)
  return StringNumberGeneric(nb, len, "0");
end;

StringNumberSpace:=function(nb,len)
  local h, idx, TheStr, U;
  if nb>=0 then
    return StringNumberGeneric(nb,len," ");
  fi;
  h:=-nb;
  if h > 10^(len-1)-1 then
    Error("the number is greater than the allowed size");
  fi;
  idx:=1;
  while(true)
  do
    if h < 10^(idx) then
      TheStr:="";
      for U in [1..len-1-idx]
      do
        TheStr:=Concatenation(TheStr, " ");
      od;
      TheStr:=Concatenation(TheStr, "-");
      return Concatenation(TheStr, String(h));
    fi;
    idx:=idx+1;
  od;
end;

GetSizeInCharacterOfNumber:=function(nb)
  local idx;
  idx:=1;
  while(true)
  do
    if nb < 10^(idx) then
      return idx;
    fi;
    idx:=idx+1;
  od;
end;




POL_VectorString:=function(eVect)
  local eStr, i;
  eStr:="[";
  for i in [1..Length(eVect)]
  do
    if i>1 then
      eStr:=Concatenation(eStr, ",");
    fi;
    eStr:=Concatenation(eStr, String(eVect[i]));
  od;
  eStr:=Concatenation(eStr, "]");
  return eStr;
end;


STRING_Split:=function(eStr, ePat)
  local lenStr, lenPat, lenTest, ListMatch, i, eStrPart, ListStrInter, iVal, eVal, FirstVal, nbMatch, eStrInter;
  lenStr:=Length(eStr);
  lenPat:=Length(ePat);
#  Print("lenStr=", lenStr, " lenPat=", lenPat, "\n");
  ListMatch:=[];
  lenTest:=lenStr - (lenPat-1);
  for i in [1..lenTest]
  do
    eStrPart:=eStr{[i..i+lenPat-1]};
#    Print("i=", i, " eStrPart=", eStrPart, "\n");
    if eStrPart=ePat then
      Add(ListMatch, i);
    fi;
  od;
  nbMatch:=Length(ListMatch);
  if nbMatch=0 then
    return rec(ListStrInter:=[eStr], ListMatch:=[]);
  fi;
  Print("nbMatch=", nbMatch, "\n");
  ListStrInter:=[];
  for iVal in [1..nbMatch]
  do
    eVal:=ListMatch[iVal];
    if eVal>1 then
      if iVal>1 then
        FirstVal:=ListMatch[iVal-1]+lenPat;
      else
        FirstVal:=1;
      fi;
      eStrInter:=eStr{[FirstVal..eVal-1]};
      Add(ListStrInter, eStrInter);
    fi;
    if iVal=nbMatch then
      if eVal+lenPat<lenStr then
        FirstVal:=eVal+lenPat;
        eStrInter:=eStr{[FirstVal..lenStr]};
        Add(ListStrInter, eStrInter);
      fi;
    fi;
  od;
  return rec(ListStrInter:=ListStrInter, ListMatch:=ListMatch);
end;






STRING_SplittingByBlock:=function(ListStr, nbPerLine)
  local nbEnt, nbLine, ListStrBlock, iLine, eStrBlock, idx, iPos;
  nbEnt:=Length(ListStr);
  if nbEnt=0 then
    return [""];
  fi;
  nbLine:=UpperInteger(nbEnt / nbPerLine);
  ListStrBlock:=[];
  for iLine in [1..nbLine]
  do
    eStrBlock:="";
    for idx in [1..nbPerLine]
    do
      iPos:=nbPerLine*(iLine-1) + idx;
      if iPos<=nbEnt then
        eStrBlock:=Concatenation(eStrBlock, ListStr[iPos]);
        if iPos < nbEnt then
          eStrBlock:=Concatenation(eStrBlock, ",");
        fi;
      fi;
    od;
    Add(ListStrBlock, eStrBlock);
  od;
  return ListStrBlock;
end;






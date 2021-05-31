RemoveDuplicatePairs:=function(f,S)
n:=#S;
temp:=[];
count:=1;
for i in [1..n] do
      j:=1;
      while j lt count and S[i] ne temp[j] and f-S[i] ne temp[j] do
	       j:=j+1;
      end while;
      if j eq count then
           Append(~temp, S[i]);
           count:=count+1;
      end if;
end for;
return temp;
end function;


decompMB:=function(p,O, f)
 Ideals:=LeftIdealClasses(O);
h:=#Ideals;
 q_I:=[1/2*BlockMatrix(2,2,[Matrix([[Trace(Conjugate(x)*f[1,1]*y): y in Basis(I)]:  x in Basis(I)]),Matrix([[Trace(Conjugate(x)*f[1,2]*y): y in Basis(I)]:  x in Basis(I)]),Matrix([[Trace(Conjugate(x)*f[2,1]*y): y in Basis(I)]:  x in Basis(I)]),Matrix([[Trace(Conjugate(x)*f[2,2]*y): y in Basis(I)]:  x in Basis(I)])]): I in Ideals];
 L_I:=[LatticeWithGram(q): q in q_I];
S_I:=<<s[1]: s in ShortVectors(L_I[i], Norm(Ideals[i])*p)>: i in [1..h]>;
f_1I:=<<(f* Matrix([[&+[v[i]*Basis(Ideals[j])[i]: i in [1..4]]],[&+[v[i+4]*Basis(Ideals[j])[i]: i in [1..4]]]])*Matrix([[Conjugate(&+[v[i]*Basis(Ideals[j])[i]: i in [1..4]]),Conjugate(&+[v[i+4]*Basis(Ideals[j])[i]: i in [1..4]])]])*f)/(Norm(Ideals[j])*p): v in S_I[j]>: j in [1..h]>;
f_1:=RemoveDuplicatePairs(f,Flat(f_1I));
return f_1, #f_1;
end function;


// RemoveDuplicates:=function(S)
//   n:=#S;
// temp:=[];
// count:=1;
// for i in [1..n] do
//       j:=1;
// 	while j lt count and S[i] ne temp[j] do
// 	       j:=j+1;
// end while;
// if j eq count then
//      Append(~temp, S[i]);
//      count:=count+1;
// end if;
// end for;
// return temp;
// end function;




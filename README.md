# Supersingular
Magma code for constructing genus 2 curves with supersingular jacobian.

The file decompositions.m needs to be loaded using

load "decompositions.m";

This makes the function decompMB(p, O, f) available

Input:
-p a prime number
-O a maximal order in a quaternion Q-algebra ramified only at (p, infty)
-f a 2x2 Matrix with entries in O as in the paper

Output:
All the Matrices f_1 such that f=f_1+(f-f_1) is a decomposition as in the paper.

Method:
Uses Algorithm 1 from the paper applied to all the right ideal classes of O.

Example:

load "decompositions.m";

p:=5;

B<a,F,aF>:=QuaternionAlgebra<RationalField() | -3, -p>;

O:=MaximalOrder(B);

f:=Matrix([[p,2*F],[-2*F,p]]);

decompMB(p,O,f);


Algorithm 2 is implemented in the package files ssEllCurvEndStr.m, genus2.m.
The first file ssEllCurvEndStr.m defines the class ssEllipticCurveEndStr of supersingular elliptic curves together with four Z-linearly independent endomorphisms.

An object in this class is constructed via ssEllipticCurveEndStr(E, B, indep, indepB, FB)

Input:
- E a supersingular elliptic curve over a field containing F_{p^2}. E must be defined over F_p.
- B a quaternion algebra (needs to be isomorphic to End^0(E))
- indep is a four element tuple of endomorphisms of E (the rational functions describing these endomorphisms must be defined at the origin).
- indepB a four element tuple of elements of B
- FB an element of B corresponding to geometric Frobenius

Output:
Creates an object with class ssEllipticCurveEndStr. The elliptic curve E has an endomorphism structure B-> End^0(E) given by mapping indepB[i] to indep[i]. FB has to map to the geometric Frobenius.

In the second file genus2.m we implemented Algorithm 2. For this one uses the intrinsic MoretBailly(Str, f, f1,f2,f_1,f_2)

Input:
- Str an object of ssEllipticCurveEndStr. For the current implementation the ground field of E must be F_{p^2}.
-  f, f1,f2,f_1,f_2 are 2x2 Matrices with entries in B.

Output:
Hyperelliptic models for the irreducible fibers of the Moret-Bailly family C->P^1 constructed from E, f.

Method:
Uses Algorithm 2 from the paper.



Example:

Attach("ssEllCurvEndStr.m");

Attach("genus2.m");

p:=5;

E:= EllipticCurve([GF(p^2)| 0,1]);

B<aB,FB, aFB>:=QuaternionAlgebra<RationalField()| -3,-p>;

zeta3:= map<E-> E | [GF(25).1^8*E.1, E.2,E.3]>;
  
F:= map<E->E | [E.1^p,E.2^p,E.3^p]>;
  
zeta3F:=F*zeta3;
  
Str:=ssEllipticCurveEndStr(E,B,[IdentityMap(E), zeta3, F, zeta3F],[B| 1, (1+aB)/2, FB,(1+aB)* FB/2],FB);
  
f:=Matrix([[5,2*FB],[-2*FB,5]]);
  
f1:=Matrix([[4,2*FB],[-2*FB,5]]);
  
f2:=f-f1;
  
f_1:=Matrix([[5,2*FB],[-2*FB,4]]);
  
f_2:=f-f_1;
  
MoretBailly(Str,f,f1,f2,f_1,f_2);

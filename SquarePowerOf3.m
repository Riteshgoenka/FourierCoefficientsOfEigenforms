/**************************************************************************************************************
 * We solve the equation \tau_k(p) + 3^\beta \sqrt{3} = (2 + \sqrt{3})^a (U + V \sqrt{3})^{k-1}, 0 <= a < (k-1)
 * ************************************************************************************************************/

load "ThueMahlerSolver.m";

for k in {18, 20} do
	for a in [0..(k-2)] do
		print "*******************************";
		print k, a;
		print "*******************************";

		QUV<U,V>:=PolynomialRing(Rationals(),2);

		QUVT<T>:=PolynomialRing(QUV);

		_<th>:=quo<QUVT | T^2-3>;

		eps1:=U+V*th;
		eps2:=U-V*th;

		Es:=Eltseq((2+th)^a*th*eps1^(k-1) - (2-th)^a*th*eps2^(k-1));
		F:=Es[1];
		G:=F div (6);
		print G;
		Zx<x>:=PolynomialRing(Integers());
		f:=Evaluate(G,[x,1]);
		clist:=Coefficients(f);
		clist:=[Integers()!c : c in clist];

		// SetClassGroupBounds("GRH");

		time solveThueMahler(clist,1,[3]);
	end for;
end for;

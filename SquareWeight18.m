/*************************************************************
 * We solve the equation tau_{18}(p)^2-p^17 = \kappa \cdot q^b
 * ***********************************************************/

sieve:=function(kappa,q);
	assert IsPrime(q);
	assert IsOdd(q);
	assert IsOdd(kappa);
	assert Valuation(kappa,q) eq 0;
	rad := &*PrimeDivisors(AbsoluteValue(kappa));
	levels:=[ 2^5*rad*q ];
	bads:=[* *];
	for level in levels do
		NFs:=Newforms(CuspForms(level));
		// print "There are", #NFs, "conjugacy classes of newforms at level", level;
		// print "with factorization", Factorisation(level);
		for i in [1..#NFs] do
			f:=NFs[i,1];
			// print "Dealing with", i, "-th newform";
			K:=NumberField(Parent(Coefficient(f,1)));
			// print "Coefficient field is", K;
			if Degree(K) eq 1 then
				// print "corresponding to elliptic curve", EllipticCurve(f);
				// print CremonaReference(EllipticCurve(f));
			end if;
			L:=PrimesInInterval(3,200);
			Exclude(~L,17);
			Exclude(~L,q);
			L:=[l : l in L | l in PrimeDivisors(kappa) eq false];
			M:=612;
			L:=[l : l in L | IsDivisibleBy(M,Order(GF(l)!q))];
			if Valuation(level,q) eq 0 then
				D:=[b: b in [0..(M-1)] | IsDivisibleBy(b,17) eq true];
			else
				D:=[b: b in [0..(M-1)] | IsDivisibleBy(b,17) eq false];
			end if;
			D1:=[b : b in D | kappa*(Integers(4)!q)^b eq 3];
			D3:=[b : b in D | kappa*(Integers(4)!q)^b eq 1];
			for l in L do
				if l in [3,5,7,11,13] eq false then
					prs:={<s,t> : t,s in GF(l) | s*(t^2-s^17) ne 0};
				elif l eq 3 then
					prs:={<s,s+1> : s in GF(l)};
				elif l eq 5 then
					prs:={<s,s^2*(s+1)> : s in GF(l)};
				elif l eq 7 then
					prs:={<s,s*(s^3+1)> : s in GF(l)};
				elif l eq 11 then
					prs:={<s,s*(s^5+1)> : s in GF(l)};
				elif l eq 13 then
					prs:={<s,s*(s^3+1)> : s in GF(l)};
				end if;
				prs:={pr : pr in prs | pr[1]*(pr[2]^2-pr[1]^17) ne 0};
				Cl1:=[];
				Cl3:=[];
				for pr in prs do
					E3:=EllipticCurve([0,2*pr[2],0,pr[1]^17,0]);			// p = 3 mod 4
					E1:=EllipticCurve([0,2*pr[2],0,pr[2]^2-pr[1]^17,0]);	// p = 1 mod 4
					if IsDivisibleBy(Integers()!(Norm(Trace(E3)-Coefficient(f,l))),17) then
						Include(~Cl3,(pr[2]^2-pr[1]^17));
					end if;
					if IsDivisibleBy(Integers()!(Norm(Trace(E1)-Coefficient(f,l))),17) then
						Include(~Cl1,(pr[2]^2-pr[1]^17));
					end if;
				end for;
				D3:=[b : b in D3 | kappa*(GF(l)!q)^b in Cl3];
				D1:=[b : b in D1 | kappa*(GF(l)!q)^b in Cl1];
				// print l,D1,D3;
				if #D1 eq 0 and #D3 eq 0 then
					break;
				end if;
			end for;
			if #D1 ne 0 or #D3 ne 0 then
				bads:=bads cat [* [* kappa, q, level , D1, D3, K, f *] *];
			end if;
		end for;
	end for;
	return bads;
end function;

bads:=[* *];
for q in {5, 17, 37} do
	print "q=", q;
	bads:=bads cat sieve(1,q);
	bads:=bads cat sieve(-1,q);
	print "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

bads;
class EigenDecomp(SageObject):

	def __init__(self,Ms,chi,pp=None):
		if (not (type(Ms) is list)) and (not (type(Ms) is sage.structure.sequence.Sequence_generic)):
			Ms = [Ms]
		self._spaces = Ms
		self._chi = chi
		if len(Ms) != 0:
			self._p = Ms[0].base_ring().characteristic()
		else:
			self._p = None
		self._pchi = pp #chosen prime over p

	def p(self):
		return self._p

	def chi(self):
		return self._chi

	def spaces(self):
		return self._spaces

	def num_spaces(self):
		return len(self.spaces())

	def __repr__(self):
		return repr(self._spaces)

	def __getitem__(self,j):
		return self._spaces[j]

	##Throw away space M
	def remove(self,M):
		self._spaces.remove(M)

	def hecke_polynomial(self,ell):
		ans = 1
		for j in range(self.num_spaces()):
			ans *= self[j].hecke_polynomial(ell)
		return ans

	## returns the irreducible factor of T_ell on j-th space 
	def hecke_irred(self,j,ell):
		facts = self[j].hecke_polynomial(ell).factor()
		assert len(facts)==1, "Not irreducible in hecke_irred!"
		return facts[0][0]

	def dimension(self):
		ans = 0
		for j in range(self.num_spaces()):
			ans += self[j].dimension()
		return ans

	## this is the degree of the smallest field over which all eigenvectors are defined
	def core_dimension(self,j,exclude,sturm=None):
		M = self[j]
		d = M.dimension()
		if sturm == None:
			sturm = STURM # M.sturm_bound()
		hp_degs = []
		for ell in primes(sturm):
			if exclude.count(ell) == 0:
				f_ell = self.hecke_irred(j,ell)
				hp_degs += [f_ell.degree()]
		return max(hp_degs)



	## returns the multiplicity that the j-th space occurs wrt Hecke algebra with primes in exclude excluded
	def multiplicity(self,j,exclude,sturm=None):
		d = self[j].dimension()
		return d / self.core_dimension(j,exclude,sturm=sturm)

	## returns the dimension of the true eigenspace of j-th space occurs wrt Hecke algebra with primes in exclude excluded
	def eigen_multiplicity(self,j,exclude,sturm=None):
		M = self[j]
		d = M.dimension()
		if sturm == None:
			sturm = STURM 
		for ell in primes(sturm):
			if exclude.count(ell) == 0:
				T = M.hecke_operator(ell)
				f = T.charpoly().factor()[0][0]
				M = f.substitute(T).kernel()
		return M.dimension() / self.core_dimension(j,exclude)

	def hecke_polys(self,j,ps=None,exclude=None,sturm=None,verbose=False):
		if ps == None:
			if sturm == None:
				sturm = STURM # self[j].sturm_bound()
			if exclude != None:
				ps = [q for q in primes(sturm) if exclude.count(q)==0]
			else:		
				ps = [q for q in primes(sturm)]
		ans = {}
		for q in ps:
			if verbose > 2:
				print "In hecke_poly q =",q
			ans[q] = self.hecke_irred(j,q) 
		return ans

	### CHEATING HERE!!!!!  ONLY COMPARING WITH MIN POLY AND 	

	## polys is a dictionary with polys[q] = min_poly of ev
	def hecke_occurs(self,polys):
		ps = polys.keys()
		occurs = False
		j = 0
		while not occurs and j < self.num_spaces():
			h_ev = self.hecke_polys(j,ps=ps)
#			occurs = h_ev == polys
			occurs = true
			for q in h_ev.keys():
				occurs = occurs and polys[q] % h_ev[q] == 0
			j += 1
		return occurs,j-1


	def remove_CM(self):
		chi = self.chi()
		if self.num_spaces() == 0 or CM.keys().count(chi)==0:
			return self			
		else:
			sturm = STURM 
			p = self.p()

			for f in CM[chi]:
				L = f.base_ring()
				pp = L.prime_above(p)
				kk = pp.residue_field()
				polys = {}
				for q in primes(sturm):
					if q != p:
						polys[q] = kk(f[q]).minpoly()
#				print polys
#				print self.hecke_polys(0)
## PROBLEM HERE: SEE ABOVE
				bool,ind = self.hecke_occurs(polys)
				if bool:
					self.remove(self[ind])
#					print "removed CM at",chi

	# def remove_non_Artin(self):
	# 	chi = self.chi()
	# 	sturm = STURM
	# 	for r in range(self.num_spaces()):
	# 		h = self.hecke_polys()
	# 		R = h[2].parent()
	# 		x = R.gen()
	# 		remove = false
	# 		q = 2
	# 		while not remove and q < sturm:
	# 			if chi.modulus() % q != 0:
	# 				v = FC.possible_Artin_polys(h[q],chi(q),p)
	# 			elif N.valuation(q) == chi.conductor().valuation(q):
	# 				v = FC.possible_Artin_polys(g,chi,p)
	# 			elif h[q] == x:
	# 				v = [x]
	# 			else:
	# 				v = []
	# 			v = [P for P in v if P.degree() <= M.dimension()]  ## weak galois conjugate check
	# 			remove = len(v) == 0
	# 			q = next_prime(q)
	# 		if remove:
	# 			self.remove(self[q])


	# def remove_eisen(self,chi):
	# 	if self.num_spaces() == 0:
	# 		return self
	# 	else:
	# 		sturm = STURM # self[0].sturm_bound()
	# 		N = chi.modulus()
	# 		p = self.p
	# 		assert chi.order() == 2

	# 		dred = {}
	# 		for q in primes(sturm):
	# 			if q != p:
	# 				dred[q] = GF(p)(chi(q)+1).minpoly()
	# 		bool,j = self.hecke_occurs(dred)
	# 		if bool:
	# 			self.remove(j)

	def lift_to_char0_minpolys(self,j,exclude=[],sturm=None):
		chi = self.chi()
		p = self.p()
		N = chi.modulus()
		h = self.hecke_polys(j,exclude=[p],sturm=sturm)
		R = PolynomialRing(QQ,'x')
		x = R.gen()
		h0 = {}
		fail = false
		### Getting minpolys away from p
		for q in h.keys():
			if q != p and exclude.count(q) == 0:
				h0[q] = FC.possible_Artin_polys(h[q],chi,q,p)
				if len(h0[q]) == 0:
					fail = true

		if exclude.count(p) == 0:
			### Here's how we handle p
			### 
			pi_p = self[j].hecke_polynomial(p)
			ans = find_ap_minpoly(pi_p)
			h0[p] = FC.possible_Artin_polys(ans,chi,p,p)
			if len(h0[p]) == 0:
				fail = true
			
		### mild galois conjugate check
		for q in h0.keys():
			if q != p:
				h0[q] = [P for P in h0[q] if 2 * P.degree() <= self.dimension() * euler_phi(chi.order())]  ## is this right at p?

		return weight_one_form(chi,h0,space=EigenDecomp(self[j],self.chi(),self._pchi)),not fail

	def upper_bound(self):
		ans = 0
		for j in range(self.num_spaces()):
			ans += floor(self[j].dimension() * self[j].base_ring().degree() / 2)
		return ans

	def lower_bound(self):
		chi = self.chi()
		if CM.keys().count(chi)==0:
			return 0
		else:
			return len(CM[chi])

	def unique_lift(self,j):
		bool = true
		ts = self.Artin_types(j)

		bool = len(ts)==1

		if bool:
			G = ts[0]
			f = self.lift_to_char0_minpolys(j,G)
			r = 0
			while bool and r < len(f.keys()):
				q = f.keys()[r]
				bool = bool and len(f[q])==1
				r += 1

		return bool 


	def grab_eigens(self,j,Kf=None,sturm=None,verbose=false):
		p = self.p()
		kk = self[j].base_ring()

		h = self.hecke_polys(j,exclude=[p],sturm=sturm,verbose=verbose)

		if Kf == None:
			R = PolynomialRing(kk,'x')
			ans = 1
			for q in h.keys():
				ans *= R(h[q])

			d = 1
			fs = ans.factor()
			for Q in fs:			
				d = lcm(d,Q[0].degree())

			if d>1:
				F = kk.extension(d,'a')
			else:
				F = kk

			phibar = Hom(kk,F)[0]  ## what am I choosing here???? CHECK THIS!
			pf = None
		else:
			pf = Kf.prime_above(p)
			kf = pf.residue_field()
			phibar = Hom(kk,kf)[0]
			F = kf

		M = self[j]
		d = M.dimension()
		V = F**d 
		W = V
		Ws = [W]
		r = 0
		while W.dimension() > 2 and r < len(h.keys()):		
			q = h.keys()[r]
			if q != self.p():
				if verbose > 2:
					print "in grab-eigens with q =",q
				T = M.hecke_operator(q)
				A = T.matrix()
				A = A.apply_map(phibar)
				for WW in Ws:
					A = A.restrict(WW)
#				A = A.restrict(W)
				W = A.left_eigenspaces()[0][1]
				Ws.append(W)
			r += 1

		fail = W.dimension()<2
		if fail:
			print "failed in grab!"
		## confused here by the 190 example but maybe dimension can still be 1 at this point

		evs = {}
		for q in h.keys()+[p]:
			if verbose > 1:
				print "In grab with q =",q

			T = M.hecke_operator(q)
			A = T.matrix()
			A = A.apply_map(phibar)
			for WW in Ws:
				A = A.restrict(WW)
			if q != self.p():
				evs[q] = A.charpoly().roots()[0][0]
			else:
				f = A.charpoly()
				ap = -f[1]
				evs[q] = ap

		return evs,pf,phibar,not fail

	def wt1_space(self,sturm=None):
		forms = []
		for r in range(self.num_spaces()):
			f,bool = self.lift_to_char0_minpolys(r,sturm=sturm)
			if bool:
				forms += floor(self[r].dimension()/2) * [f]

		return weight_one_space(forms)
	


# def eigen_system(M,sturm):
# 	ans = {}
# 	p = M.base_ring().characteristic()
# 	for q in primes(sturm):
# 		if q != p:
# 			ans[q] = M.hecke_polynomial(q).roots()[0][0]
# 		else:
# 			ans[q] = -M.hecke_polynomial(q)[1]

# 	return ans




def unique(d):
	bool = true
	for q in d.keys():
		bool = bool and len(d[q])==1
	return bool




# ## this code looks like it doesn't work in general (greedy algorithm in finding hecke system)
# def cut_out_eigen(chi,f,p):
# 	v = f.values()
# 	v = [a[0] for a in v]
# 	Q = prod(list(set(v)))
# 	L = Q.splitting_field('alpha')
# 	ppL = L.prime_above(p)
# 	kL = ppL.residue_field()
# 	print "Splitting field",kL

# 	K = CyclotomicField(chi.order())
# 	ppK = K.prime_above(p)
# 	kK = ppK.residue_field()
# 	phi = Hom(kK,kL)[0]
# 	print kK,kL,phi,chi
# 	chip = chi.change_ring(kK).change_ring(phi)

# 	print "Forming ModularSymbols"

# 	M = ModularSymbols(chip,p,1,kL).cuspidal_subspace()

# 	r = 0
# 	done = false
# 	R = PolynomialRing(kL,'x')

# 	print "Cutting down over extension field"
# 	r = 0
# 	while not done and r < len(f.keys()):
# 		q = f.keys()[r]		
# 		if q != p:
# 			print "prime =",q
# 			T = M.hecke_operator(q)
# 			aqs = R(f[q][0]).roots()
# 			print aqs
# 			bool = true
# 			j = 0
# 			while bool:
# 				print "Trying",j,":",aqs[j]
# 				MM = (T-aqs[j][0]).kernel()
# 				print "Dim =",MM.dimension()
# 				bool = MM.dimension() < 2
# 				j += 1
# 			M = MM
# 			done = M.dimension() == 2
# 		r += 1

# 	assert M.dimension()==2,"dim too large"
# 	print "Done"
# 	return M


def find_ap_minpoly(pi_p):
	F,phi = pi_p.splitting_field('a',map=true)
	rs = pi_p.map_coefficients(phi).roots()
	assert len(rs) <= 2 and len(rs)>=1,"problem at p in find_ap_minpoly"
	alpha = rs[0][0]
	if len(rs) == 1:  ## alpha = beta
		ans = (2*alpha).minpoly()
	else:
		beta = rs[1][0]
		ans = (alpha+beta).minpoly()
	return ans
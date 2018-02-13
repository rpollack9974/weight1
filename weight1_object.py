class wt1(SageObject):
	"""This is the main class of weight 1 forms

	The following explained in the stored data in this class:

	self._neben = nebentype character
	self._CM = list of the CM forms (including oldforms) which have not yet been excluded
				these forms can be excluded by 
					(a) not looking "new" at level N -- i.e. a_ell non-zero for supercuspidal ell
					(b) 
	"""
	def __init__(self,chi):
		self._neben = chi
		self._Qchi = chi.base_ring()
		if self._Qchi == QQ:
			self._Qchi = CyclotomicField(2)

		self._CM = []
		self._old_exotic = []

		self._upper = Infinity
		self._lower = 0

		self._spaces = []

		self._locally_constained = False
		self._bad_primes = []
		self._steinberg_primes = []
		self._bad_rps_primes = []

		self._fully_computed = False

		self._forms = []

		self.compute_space()

	def __repr__(self):
		print "Space is fully computed:",self.is_fully_computed()
		print "Space is locally constrained:",self.is_locally_constrained()
		if self.is_locally_constrained():
			print "   Steinberg primes:",self.steinberg_primes()
			print "   Bad RPS primes:",self.bad_rps_primes()
			print "   All bad primes:",self.bad_primes()
		if self.is_fully_computed():
			print "There are",self.num_forms(),"form(s)."
		else:
			print "Not fully computed"
			print "Lower bound =",self.lower_bound()
			print "Upper bound =",self.upper_bound()

		return repr("Space of weight 1 forms with nebentype "+str(self.neben()))

	### THIS IS THE MAIN FUNCTION
	def compute_space(self):
		self.check_local_constraints()
		if self.is_fully_computed():
			return

		# don't want to recursively compute old exotic here as info (of none there) might come for free
		# so we only count the number of already pre-computed forms (if any)
		self.compute_lower_bound_from_old_exotic()
		self.compute_CM()

		self.cut_down_to_unique()
		if self.is_fully_computed():
			return

		self.excise_CM_forms()
		self.compute_bounds()
		if self.is_fully_computed():
			return

		self.excise_old_exotic_forms()
		self.compute_bounds()
		if self.is_fully_computed():
			return

		self.verify_remaining_forms()

		assert 0==1,str(self)

	def Qchi(self):
		return self._Qchi

	def neben(self):
		return self._neben

	def upper_bound(self):
		return self._upper

	def lower_bound(self):
		return self._lower

	def set_upper_bound(self,U):
		self._upper = U
		if self.upper_bound() == self.lower_bound():
			self.set_to_fully_computed()

	def set_lower_bound(self,L):
		self._lower = L
		if self.upper_bound() == self.lower_bound():
			self.set_to_fully_computed()

#####FUNCTIONS ABOUT SPACES FIELD
	def space(self,i):
		return self._spaces[i]

	def spaces(self):
		return self._spaces

	def set_spaces(self,spaces):
		self._spaces = spaces
		self.compute_bounds()

	def add_space(self,S):
		self._spaces += [S]

	def replace_space(self,S,i):
		self._spaces[i] = S

	def num_spaces(self):
		return len(self.spaces())

	### true if there exists a space with min polys uniquely determined
	def is_unique(self):
		unique = false
		for S in self.spaces():
			unique = unique or S.unique()
		return unique

	def unique_space(self):
		assert self.is_unique(),"no unique space here!"
		for S in self.spaces():
			if S.unique():
				return S

	### if not all minpolys are unique in any space, just return the minimum number of forms in any space
	### if there is some space with a unique min polys, then first minimal multiplicity by form across unique spaces
	def compute_upper_bound(self):
		U = min([S.num_forms() for S in self.spaces()])
		if not self.is_unique():
			self.set_upper_bound(U)
			return
		else:
			if self.num_spaces() == 0:
				self.set_upper_bound(Infinity)
				return
			else:
				T = self.unique_space()
				ans = 0
				used_forms = []
				for f in T:
					if used_forms.count(f) == 0:
						m = min([S.multiplicity(f) for S in self.spaces() if S.unique()])
						ans += m
						used_forms += [f]
				self.set_upper_bound(min(ans,U))
				return

	def has_unramified_prime(self):
		primes_used = self.primes_used()
		S = self.unique_space()
		unramified_prime = true
		for f in S:
			bool = false
			d = 1
			for q in f.primes():
				d *= f[q][0].discriminant().norm()
			for q in primes_used:
				bool = bool or d % q != 0
			unramified_prime = unramified_prime and bool
		return unramified_prime

	def space_at_p(self,p):
		primes_used = self.primes_used()
		assert primes_used.count(p) > 0,"mod "+str(p)+" space not yet computed!"

		for S in self.spaces():
			if S.p() == p:
				break
		return S

#######################
	def CM(self):
		return self._CM

	def old_exotic(self):
		return self._old_exotic

	def add_CM(self,f):
		self._CM += [f]

	def remove_CM(self,f):
		self._CM.remove(f)

	def set_CM(self,list_of_CM):
		self._CM = list_of_CM

	def add_old_exotic(self,f):
		self._old_exotic += [f]

	def is_fully_computed(self):
		return self._fully_computed

	def set_to_fully_computed(self):
		self._fully_computed = True

	def is_locally_constrained(self):
		return self._locally_constained

	def set_to_locally_constained(self):
		self._locally_constained = True
		self._fully_computed = True

	def bad_primes(self):
		return self._bad_primes

	def add_bad_prime(self,ell):
		self._bad_primes += [ell]

	def steinberg_primes(self):
		return self._steinberg_primes

	def add_steinberg_prime(self,ell):
		self._steinberg_primes += [ell]
		self.add_bad_prime(ell)

	### rps = ramified principal series; bad = order of character at prime > 5
	def bad_rps_primes(self):
		return self._bad_rps_primes

	def add_bad_rps_prime(self,ell):
		self._bad_rps_primes += [ell]
		self.add_bad_prime(ell)

	def forms(self):
		return self._forms

	def num_forms(self):
		return len(self.forms())

	def compute_lower_bound(self):
		return self.set_lower_bound(len(self.CM()))

	def compute_bounds(self):
		self.compute_upper_bound()
		self.compute_lower_bound()


	### checks to see:
	###		(a) whether or not nebentype is odd
	###		(b) if there are any Steinberg primes
	###		(c) if there are any bad ramified principal series primes
	def check_local_constraints(self):
		chi = self.neben()
		if chi(-1) == 1:			
			self.add_bad_prime(Infinity)
			self.set_to_locally_constained()

		N = chi.modulus()
		for ell in prime_divisors(N):
			if steinberg(chi,ell):
				self.add_steinberg_prime(ell)
				self.set_to_locally_constained()
			if bad_rps(chi,ell):
				self.add_bad_rps_prime(ell)
				self.set_to_locally_constained()

	### computes dimension of old_exotic forms from data stored in exotic -- no extra computations done
	def compute_lower_bound_from_old_exotic(self):
		chi = self.neben()
		N = chi.modulus()
		Nc = chi.conductor()
		lb = 0
		divs = divisors(N/Nc)
		divs.remove(N/Nc)  # proper divisors of N/Nc
		for d in divs:
			G_old = DirichletGroup(Nc * d)
			chi_old = G_old(chi)
			chi_old = chi_old.minimize_base_ring()
			if exotic.has_key(chi_old):
				for f in exotic[chi_old]:
					lb += multiplicity_from_oldspace(f,N)  ### chi should be contained in data of f I guess
		self.set_lower_bound(self.lower_bound()+lb)

	def compute_CM(self):
		print "Computing CM"
		chi = self.neben()
		N = chi.modulus()
		Nc = chi.conductor()
		
		for d in divisors(N/Nc):
			G_old = DirichletGroup(Nc * d)
			Nt = N / (Nc * d)
			chi_old = G_old(chi)
			chi_old = chi_old.minimize_base_ring()
			if CM.has_key(chi_old):
				for F in CM[chi_old]:
					f = F[0]
					phi = F[2]
					olds = oldspan(f,N,chi_old,phi)
					### oldspan returns 3-tuples: (form,phi,multiplicity)
					for g in olds:
						self.add_CM(g)
		self.compute_lower_bound()

	def primes_used(self):
		return [S.p() for S in self.spaces()]

	## find non-supercuspidal prime
	def next_good_prime(self):
		chi = self.neben()
		N = chi.modulus()
		Nc = chi.conductor()
		primes_used = self.primes_used()
		if len(primes_used) == 0:
			p = 2
		else:
		    p = next_prime(max(primes_used))
		while N.valuation(p) != Nc.valuation(p):
			p = next_prime(p)

		return ZZ(p)

	def use_new_prime(self,p,log=None,verbose=False):
		sturm = STURM
		chi = self.neben()
		N = chi.modulus()

		Sp = wt1_space_modp(p,chi,verbose=verbose,log=log)

		for Sq in self.spaces():
			Sp = Sp.intersect(Sq)
		for i in range(self.num_spaces()):
			self.replace_space(self.space(i).intersect(Sp),i)
		for Sq in self.spaces():
			Sp = Sp.intersect(Sq)
		for i in range(self.num_spaces()):
			self.replace_space(self.space(i).intersect(Sp),i)
		self.add_space(Sp)
		self.compute_bounds()
		return 

	def cut_down_to_unique(self,log=None,verbose=false):
		print "Cutting down to unique"
		chi = self.neben()
		sturm = STURM

		N = chi.modulus()
		Nc = chi.conductor()

		unique = false
		unramified_prime = false

		p = 1
		while (not self.is_fully_computed()) and (not self.is_unique() or not self.has_unramified_prime()):
			p = self.next_good_prime()
#			print "using",p
			self.use_new_prime(p,log=log,verbose=verbose)
			self.remove_non_Artin_CM(p)
#			print self.spaces()
		return

	def remove_non_Artin_CM(self,p):
		chi = self.neben()
		new_list = []
		for f in self.CM():
			if not self.is_non_Artin(f,p):
				new_list += [f]
		self.set_CM(new_list)
		self.compute_bounds()
		return

	def excise_old_exotic_forms(self):
		##!!
		return

	def excise_CM_forms(self,log=None,verbose=False):
		print "bounds don't meet: now removing CM from"
		sturm = STURM 
		chi = self.neben()
		N = chi.modulus()
		Qchi = self.Qchi()
		success = true
		hecke_used = []
		for F in self.CM():
			f = F[0]
			print "trying CM",f
			phi = F[1]
			CM_mult = F[2]
			h = {}
			for q in f.keys():
				if q < sturm:
					h[q] = [minpoly_over(f[q],Qchi,phi)]
			print "working on",f,"--",h
			if hecke_used.count(h) == 0:
				excised = false
				hecke_used += [h]
				for S in self.spaces():
					if S.unique():
						p = S.p()
#						e = scaling(N,p)
						print "p =",p
						hp = deepcopy(h)
						if hp.has_key(p):
							hp.pop(p)
						modp_mult = S.hecke_multiplicity(h)
						dp = max_degree(hp)
						print "have",modp_mult,"copies of this form and am expecting",CM_mult*dp
						assert modp_mult >= dp * CM_mult,"CM/old not found!!"+str(f)+str(self)
						if modp_mult == CM_mult * dp:
							### multiplicity exactly correct so we can throw away these CM forms safely
							print "can safely remove the CM/old form "+str(f)
							output(log,verbose,3,"can safely remove the CM/old form "+str(f))
							self.fully_excise_CM_form(h)
							excised = true
							break
				if not excised:
					print "not enough --- checking up to strong_sturm for CM/old with p =",p
					### there are potentially forms congruent to this CM form in weight p which don't come from weight 1
					### but we now are careful and check to the sturm bound to prove this congruence
					p,bool = self.good_CM_cut_out_prime()
					S = self.space_at_p(p)
					assert bool,"need to program when there is no good prime here"
#					e = scaling(N,p)
					hp = deepcopy(h)
					if hp.has_key(p):
						hp.pop(p)
					dp = max_degree(hp)
					modp_mult = self.true_modp_mult(p,hp)
					a = self.generalized_eigenspace_dimension(p,f,phi,modp_mult)
					assert a * dp <= modp_mult, "something wrong here"
					if a * dp == modp_mult:
						print "Found that the",a*dp,"CM forms fill up the",modp_mult,"-dimensional generalized eigenspace"
						print "after careful check removing the CM/old form "+str(f)
					 	output(log,verbose,3,"after careful check removing the CM/old form "+str(f))
					 	self.fully_excise_CM_form(h)
					else:
					 	print "couldn't remove the CM/old form",f
					 	success = false
		return success

	def good_CM_cut_out_prime(self):
		ps = [S.p() for S in self.spaces() if S.unique()]
		### 2 is no good because there could be congruences between CM and exotic
		if ps.count(2) > 0:
			ps.remove(2)
		if len(ps) == 0:
			return 0,false
		else:
			return min(ps),true

	def true_modp_mult(self,p,hp):
		chi = self.neben()
		pchi = FC.pchi(p,chi)
		kchi = pchi.residue_field()
		M = ModularSymbols(chi,p,1,kchi).cuspidal_subspace()
		R = PolynomialRing(kchi,'x')
		for q in hp.keys():
			Tq = M.hecke_operator(q)
			M = (R(hp[q][0]).substitute(Tq)**M.dimension()).kernel()
		return M.dimension()

	def generalized_eigenspace_dimension(self,p,f,phi,modp_mult):
		sturm = STURM
		chi = self.neben()
		N = chi.modulus()
		Qchi = self.Qchi()
		z = Qchi.gen()
		pchi = FC.pchi(p,chi)
		kchi = pchi.residue_field()
		Kf = f[f.keys()[0]].parent()
		pf = Kf.prime_above(p)
		kf = pf.residue_field()
		H = Hom(kchi,kf)
		for phibar in H:
			if phibar(kchi(z)) == kf(phi(z)):
				break
		chip = chi.change_ring(phibar)
		if N % p != 0 and f.has_key(p):
				ap = f[p]
				R = PolynomialRing(kf,'x')
				x = R.gen()
				pibar_p = x**2-kf(ap)*x+chip(p)
				if len(pibar_p.roots()) == 0:
					lf,phibar_lf = pibar_p.splitting_field('a',map=true)
					M = ModularSymbols(chip,p,1,lf).cuspidal_subspace()
				else:
					M = ModularSymbols(chip,p,1,kf).cuspidal_subspace()
		else:
			M = ModularSymbols(chip,p,1,kf).cuspidal_subspace()

		for q in primes(sturm):
			if q != p or N % p == 0:
				Tq = M.hecke_operator(q)
				M = ((Tq-kf(f[q]))**(2*modp_mult)).kernel()

		if p < sturm and N % p != 0:
			Tp  = M.hecke_operator(p)
			if len(pibar_p.roots()) == 1:
				alpha = pibar_p.roots()[0][0]
				M = ((Tp-alpha)**(2*modp_mult)).kernel()
				a = M.dimension()
			elif len(pibar_p.roots()) == 2:
				alpha = pibar_p.roots()[0][0]
				Ma = ((Tp-alpha)**(2*modp_mult)).kernel()
				beta = pibar_p.roots()[1][0]
				Mb = ((Tp-beta)**(2*modp_mult)).kernel()
				a = Ma.dimension() + Mb.dimension()
			else:
				alpha = hom_to_poly(pibar_p,phibar_lf).roots()[0][0]
				M = ((Tp-alpha)**(2*modp_mult)).kernel()
				a = M.dimension()

		return a

	### checks if the modular form (actually 3-tuple (form,phi,multiplicity)) is 
	def is_non_Artin(self,f,p):
		print "CHecking if",f[0],"is Artin at p =",p
		chi = self.neben()
		pchi = FC.pchi(p,chi)
		phi = f[1]
		f = f[0]
		sturm = STURM
		for ell in primes(sturm):
			P = minpoly_over(f[ell],chi.base_ring(),phi)
			kchi = pchi.residue_field()
			R = PolynomialRing(kchi,'x')
			print ell,":",gcd(R(prod(FC[make_key(chi,ell)])),R(P))
			if gcd(R(prod(FC[make_key(chi,ell)])),R(P)) == 1:
				print "non-artin"
				return True
		print "artin"
		return False


	## h = hecke eigensystem.
	## runs through all unique spaces and finds minimal multiplicity of h
	def min_hecke_multiplicity(self,h):
		ans = Infinity
		for S in self.spaces():
			if S.unique():
				ans = min(ans,S.hecke_multiplicity(h))
		return ans

	## removes h from all unique spaces and from CM field
	def fully_excise_CM_form(self,h):
		for S in self.spaces():
			if S.unique():
				while S.hecke_multiplicity(h) > 0:
					S.remove_hecke(h)
		new_list = []
		for F in self.CM():
			f = F[0]
			phi = F[1]
			hf = {}
			for q in h.keys():
				hf[q] = [minpoly_over(f[q],self.Qchi(),phi)]
			if hf != h:
				new_list += [F]
		self.set_CM(new_list)
		return 

	def test_form(self,f):
		p = self.good_prime_for_sturm(f)
		chi = self.neben()
		N = chi.modulus()
		Qchi = self.Qchi()
		z = Qchi.gen()
		strong_sturm = ceil(Gamma0(N).index() / 3)  ### CHECK THIS!!!!
		M = f.space()[0]
		kchi = M.base_ring()
		Kf,phi = f.FC_field()
		R = PolynomialRing(Kf,'x')
		pf = Kf.prime_above(p)
		kf = pf.residue_field()
		H = Hom(kchi,kf)
		found = false


	def good_prime_for_sturm(self,f):
		d = f.disc()
		found = false
		for S in self.spaces():
			if S.unique() and d % S.p() != 0:
				found = true
				break
		assert found,"not found?"
		return S.p()


	def verify_remaining_forms(self):
		S = self.unique_space()
		for f in S:
			fq = self.form_qexp(f)
			self.verify(fq)

	def form_qexp(self,f,log=None,verbose=False):
		fs = []
		for S in self.spaces():
			if S.unique():
				for g in S:
					if f == g:
						fs += [g]
						break
		p = f.p()
		chi = self.neben()
		N = chi.modulus()
		Qchi = self.Qchi()
		z = Qchi.gen()
		strong_sturm = ceil(Gamma0(N).index() / 3)  ###! CHECK THIS!!!!
		M = f.space()[0]
		kchi = M.base_ring()
		Kf,phi = f.FC_field()
		R = PolynomialRing(Kf,'x')
		pf = Kf.prime_above(p)
		kf = pf.residue_field()
		H = Hom(kchi,kf)
		found = false
		for phibar in H:
			if phibar(kchi(z)) == kf(phi(z)):
				found = true
				break
		assert found,"no phibar found"
		need_more_primes = false

		d = M.dimension()
		V = kf**d 
		W = V
		Ws = [W]
		q = 2
		if N % p != 0:
			e = 2
		else:
			e = 1
		while W.dimension() > e:		
			if q != p:
				output(log,verbose,2,"-in form_qexp cutting down to 2-dimensional space with q="+str(q))
				T = M.hecke_operator(q)
				A = T.matrix()
				A = A.apply_map(phibar)
				for WW in Ws:
					A = A.restrict(WW)
				W = A.left_eigenspaces()[0][1]
				Ws.append(W)
			q = next_prime(q)

		fail = (W.dimension() < 2) and (N % p != 0)  
		if fail:
			print "failed in ???!"
			return 0,0,not fail,need_more_primes,chi

		if not fail:
			output(log,verbose,2,"--finished cutting down to 2-dimensional space.  Computing e-vals now")

			evs_modp = {}
			hecke = {}
			evs = {}
			for q in primes(strong_sturm):
				output(log,verbose,2,"-in form_qexp computing mod "+str(p)+" eigenvalue at q="+str(q))

				T = M.hecke_operator(q)
				A = T.matrix()
				A = A.apply_map(phibar)
				for WW in Ws:
					A = A.restrict(WW)
				if q != p or N % p == 0:
					assert len(A.charpoly().roots()) == 1,"too many roots"
					evs_modp[q] = A.charpoly().roots()[0][0]
				elif N % p != 0: ###!! does this assume mod p mult 1 in that the space is exactly 2 dimensional???
					assert W.dimension() == 2, "mod p mult 1 failed?"
					fp = A.charpoly()
					ap = -fp[1]
					evs_modp[q] = ap

				hecke[q] = FC.possible_Artin_polys(minpoly_over(evs_modp[q],kchi,phibar),chi,q,p,upper=self.upper_bound())
				if len(hecke[q]) == 0:
					return 0,0,false,need_more_primes,chi

	#			print q,hecke[q]
				if len(hecke[q]) > 1:
					for g in fs:
						if g.p() != p:
							output(log,verbose,2,"--not uniquely determined: using p="+str(g.p())+" to help")
							Mg = g.space()[0]   ### USING ONLY THE FIRST SPACE HERE!!  IS THIS A PROBLEM???
	#						Kg,phi_g = g.FC_field()
							pg = Kf.prime_above(g.p())
							kg = pg.residue_field()
							kchi_g = Mg.base_ring()
							H = Hom(kchi_g,kg)
							found = false
							for phibar_g in H:
								if phibar_g(kchi_g(z)) == kg(phi(z)):
									found = true
									break
							assert found,"no phibar found"
							fq = Mg.hecke_polynomial(q)
							if g.p() != q:
								fq = fq.factor()[0][0]
								pi_qs = FC.possible_Artin_polys(fq,chi,q,g.p(),upper=self.upper_bound())
							else:
								pi_alpha = fq.factor()[0][0]
								pi_alpha = hom_to_poly(pi_alpha,phibar_g)
								l,phibar_g_ext = pi_alpha.splitting_field('a',map=true)  ### cgeck here!
								alpha = hom_to_poly(pi_alpha,phibar_g_ext).roots()[0][0]
								if N % g.p() != 0:
									ap = alpha + phibar_g_ext(phibar_g(kchi_g(chi(g.p()))))/alpha
								else:
									ap = alpha
								fp = minpoly_over(ap,kchi_g,compose(phibar_g_ext,phibar_g))
								pi_qs = FC.possible_Artin_polys(fp,chi,g.p(),g.p(),upper=self.upper_bound())
	#						print q,pi_qs
							if len(pi_qs) == 0:
								fail = true
								break  ###! LOOKS LIKE I"m NOT BREAKING FAR ENOUGH
							else:
								S1 = set(hecke[q])
								S2 = set(pi_qs)
								hecke[q] = list(S1.intersection(S2))
							if len(hecke[q]) == 1:
								break
							if len(hecke[q]) == 0:
								fail = true

	#			print "ans:",hecke[q]
				if fail:
					return 0,0,not fail,need_more_primes,chi

				if len(hecke[q]) != 1:
					need_more_primes = True
					break
				else:
					fq = hecke[q][0]
					rs = hom_to_poly(fq,phi).roots()
					done = false
					j = 0
					possible_lifts = [r[0] for r in rs if evs_modp[q] == kf(r[0])]
					assert len(possible_lifts)>0, "no congruent root found "+str(rs)+str(fq)
					assert len(possible_lifts)==1, "lift not unique!"
					evs[q] = possible_lifts[0]
	#				print q,evs_modp[q],evs[q],evs[q].minpoly()

			if not need_more_primes:
				R = PowerSeriesRing(Kf,'q')
				q = R.gens()[0]
				ans = 0
				for n in range(1,strong_sturm):
					ans += an(evs,n,chi,phi) * q**n

				return ans,phi,not fail,need_more_primes,chi
			else:
				output(log,verbose,1,"Min polys not uniquely determined: need to compute with more primes")
				return 0,0,not fail,need_more_primes,chi


#--------------------
### steinberg if ell divides the level exactly onece and doesn't divide conductor of chi
def steinberg(chi,ell):
	N = chi.modulus()
	Nc = chi.conductor()
	return valuation(N/Nc,ell) == 1 and valuation(Nc,ell) == 0

### ramified principal series prime if ell divides the conductor of chi with same multiplicity as ell divides the level
### bad ramified principal series prime if ell-primary part of chi has order > 5
def bad_rps(chi,ell):
	Nc = chi.conductor()
	if Nc % ell != 0:
		return false
	D = chi.decomposition()
	for chi_ell in D:		
		if chi_ell.conductor() % ell == 0:
			break
	return chi_ell.order() > 5


def supercuspidal(chi,ell):
	N = chi.modulus()
	Nc = chi.conductor()
	return N.valuation(ell) != Nc.valuation(ell)


#----------------------------------------------------------------
## f is new in S_1(Nc * d, chi) where Nc = conductor of chi
##
## returns a list of 3-tuples.  Each 3-tuple has the form:
##
##		(h,phi,m)
##
## where 
##
## -h is a dictionary mapping ell to an eigenvalue of T_ell on
## the span of {f(d'z) : d' | N/(Nc * d) } 
## -phi is a map from Q(chi) to K_f
## -m is the multiplicity of the eigenvalue
def oldspan(f,N,chi,phi):
	Nc = chi.conductor()
	d = chi.modulus() / Nc
	L = f.base_ring()
	Qchi = chi(1).parent()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	R = PolynomialRing(Qchi,'x')
	x = R.gen()
	Nt = N / (Nc * d)
	sturm = STURM

	h = {}
	for ell in primes(sturm):
		if N % ell != 0:
			h[ell] = f[ell]

	v = [[h,phi,1]]
	for ell in prime_divisors(N):
		new_v = []
		for t in v:
		### In this case a_ell(f) must be 0 and old copies of it still are 0
			if ell < sturm:
				if d % ell == 0:
					h = deepcopy(t[0])
					h[ell] = L(0)
					new_v += [[h,phi,t[2] * (valuation(Nt,ell) + 1)]]
			### In this case a_ell(f) persists as an eigenvalue of U_ell with mult 1 and 0 has rest of multiplicity		
				elif Nc % ell == 0:
					if valuation(Nt,ell) == 0:
						h1 = deepcopy(t[0])
						h1[ell] = f[ell]
						new_v += [[h1,phi,t[2]]]
					else:
						h2 = deepcopy(t[0])
						h2[ell] = L(0)
						new_v += [[h2,phi,t[2] * (valuation(Nt,ell))]]
				else: ## now ell must divide Nt with mult >= 2
					if valuation(Nt,ell) > 1:
						h3 = deepcopy(t[0])
						h3[ell] = L(0)
						new_v += [[h3,phi,t[2] * (valuation(Nt,ell)-1)]]
			else:
				new_v += [[t[0],phi,(valuation(Nt,ell) + 1)*t[2]]]
		v = new_v
	return v






def combine(all_olds,olds):
	all_forms = [f[0] for f in all_olds]
	for r in range(len(olds)):
		f = olds[r][0]
		if all_forms.count(f) > 0:
			ind = all_forms.index(f)
			all_olds[ind][1] += olds[r][1]
		else:
			all_olds += [olds[r]]
	return all_olds

def scaling(N,p):
	if N % p != 0:
		return 2
	else:
		return 1
from sage.structure.sage_object import SageObject

########################################
##  DEFINE THE BASIC WEIGHT ONE CLASS ##
########################################

######################################################################################################
##				
##  This class keeps track of potential Hecke-eigenvalues of some potential weight 1 form.
##  The eigenvalues are stored as a dictionary which takes a prime q to a list of possible
##  minimal polynomials of a_q
##                                                                                               
######################################################################################################

class weight_one_form(SageObject):
	def __init__(self,chi,hecke={},space=None):
		"""
		Returns a potential weight one form with the following data:

			_neben = nebentype of the form 
			_hecke = list of possible minimal polynomials of eigenvalues 
			_space = underlying mod p space of modular symbols which gave rise to the form
			_evs_modp = dictionary of mod p eigenvalues coming from _space (base extended to get a bonafide eigenvector)
			_evs = dictionary of eigenvalues which lift _evs_modp and satisfy (unique) polynomial in _hecke
			_q_exp = q_exp of the form (computed after getting _evs)
			_phi = choice of a map from Q(chi) to K_f (hecke eigenfield)
			-pL = choice of a prime in K_f

		INPUT:
		chi -- Dirichlet character
		hecke (optional) -- a dictionary which sends primes q to a list of irreducible polys over Q
		space (optional) -- the space which gives rise to the form

		WARNING: I DONT THINK I KEEP TRACK OF ALL OF THE OTHER DATA WHEN CREATING NEW FORMS.  MUST I?
		
		OUTPUT:
        
		A potential weight 1 form
		"""
		self._neben = chi
		self._hecke = hecke
		self._space = space
		self._evs_modp = None
		self._evs = None
		self._q_exp = None
		self._phi = None
		self._phibar = None
		self._pf = None
		if self._space != None:
			self._p = self.space().p()
		else:
			self._p = None

	def p(self):
		return self._p

	def evs_modp(self):
		return self._evs_modp

	def evs(self):
		return self._evs

	def phi(self):
		return self._phi

	def chi(self):
		return self._neben

	def q_exp(self):
		return self._q_exp

	def hecke(self,q=None,i=None):
		"""
		CHANGE HERE Returns the dictionary containing the minimum polynomial information

		INPUT:
		- none

		OUTPUT:
        
		A dictionary: q --> list of irred polys
		"""
		if q == None:
			return self._hecke
		else:
			if self._hecke.keys().count(q) > 0:
				return self._hecke[q][i]
			else:
				#### THIS IS WRONG!!!
				D = self.space()
				self._hecke[q] = [D.hecke_polynomial(q)]
				return self._hecke[q][i]

	def space(self):
		"""
		Returns the modular symbol space in weight p which gives rise to this potential weight 1 form

		INPUT:
		- none

		OUTPUT:
        
		A weight p modular symbol space in characteristic p
		"""
		return self._space

	def __cmp__(self,g):
		"""
		Checks to see if self and g are identically the same (i.e. the exact same list of possible min polys)

		INPUT:
		- g -- weight_one_form

		OUTPUT:
        
		True or False
		"""

		return cmp(self.hecke(),g.hecke())

	def __repr__(self):
		"""Prints to screen the hecke infomation; returns nothing"""

#		print ""
#		for q in self.primes():
#			print q,":",self[q]
#		return repr(self.hecke())
#		return ""
		if self.q_exp() != None:
			return repr(self.q_exp())
		else:
			return repr(self.hecke())


	def __getitem__(self,q):
		"""
		Returns the possible minimal polynomials of a_q of this form.

		INPUT:
		- q -- prime (for which the q-th Hecke data is computed)

		OUTPUT:
        
		The possible minimal polynomials of a_q of this form.
		"""
		return self._hecke[q]

	def num_evals(self):
		"""
		Returns the number of Hecke-eigenvalues stored

		INPUT:
		- none

		OUTPUT:
        
		The number of Hecke-eigenvalues.
		"""

		return len(self.hecke().keys())

	def prime(self,r):
		"""
		Returns the prime associated to the r-th Hecke-eigenvalue stored.

		INPUT:
		- r -- integer (less than the number of eigenvalues stored)

		OUTPUT:
        
		The prime associated to the Hecke-eigenvalue stored in the r-th slot of our list.
		"""

		return self.hecke().keys()[r]

	def primes(self):
		"""
		Returns the list of primes for which there is a Hecke-eigenvalue stored.

		INPUT:
		- none

		OUTPUT:
        
		The list of primes for which these is Hecke data stored.
		"""
		return self.hecke().keys()

	def all_possible_hecke(self):
		"""
		Returns all possible minimal polynomials of all Hecke-eigenvalues stored.

		INPUT:
		- none

		OUTPUT:
        
		All possible minimal polynomials of all Hecke-eigenvalues stored --- output is list of lists
		"""
		return [self[q] for q in self.primes()]

	def degree(self):
		v = self.all_possible_hecke()
		w = []
		for P in v:
			w += P
		return max([P.degree() for P in w])


	def compare(self,g):
		"""
		Checks for each q (for which a_q is computed for both self and g) whether there is common min poly 
		for a_q for both forms.

		INPUT:
		- g --- weight_one_form

		OUTPUT:
        
		True or False (True is there is such a common min poly for each q)
		"""
		if self.num_evals() == 0 or g.num_evals() == 0:
			return False
		else:
			same = True
			j = 0
			while (j < self.num_evals()) and same:
				p = self.prime(j)
				if p in g.primes():
					S1 = set(self[p])
					S2 = set(g[p])					
					if S1.isdisjoint(S2):
						return S1,S2
						same = False
				j = j + 1
			return same


### MAYBE THIS IS NEVER USED???
	def intersect(self,g):
		"""
		For each q (common to both forms) finds the common min polys for both forms and produces a new weight 1 forms 
		with these min polys.

		For q that are in one form but not the other the Hecke data is simply discarded.

		INPUT:
		- g --- weight_one_form

		OUTPUT:
        
		The weight one form which is the "intersection" of both forms in the sense for each q only the min polys 
		common to both forms are kept.
		"""
		if self.compare(g):
			all_primes = list(set(self.primes()).union(set(g.primes())))

			new_possible_hecke = {}
			for ell in all_primes:
				if ell in self.primes() and ell in g.primes():
					S1 = set(self[ell])
					S2 = set(g[ell])
					new_possible_hecke[ell] = list(S1.intersection(S2))
				elif ell in self.primes():
					new_possible_hecke[ell] = self[ell]
				else:
					new_possible_hecke[ell] = g[ell]

			return weight_one_form(self.chi(),new_possible_hecke,self.space())
		else:
			return weight_one_form(self.chi(),{})

	def intersect_with_many(self,many):
		"""
		For each q, the min polys in self are kept iff they appear in some form listed in many.

		INPUT:
		- many -- a list of weight_one_form

		OUTPUT:
        
		The weight one form whose min polys appear in some form in many (a list of forms).
		"""
		many = [many[a] for a in range(len(many)) if self.compare(many[a])]

		if many == []:
			return weight_one_form(self.chi(),{})
		else:
			all_primes = self.primes()
			for g in many:
				all_primes += g.primes()
			all_primes = list(set(all_primes))

			new_possible_hecke = {}
			for ell in all_primes:
				S2 = set([])
				for g in many:
					if g.primes().count(ell) > 0:
						S2 = S2.union(set(g[ell]))
				if self.primes().count(ell) > 0:
					if len(S2) > 0:
						S1 = set(self[ell]).intersection(S2)
					else:
						S1 = self[ell]
				else:
					S1 = S2
				new_possible_hecke[ell] = list(S1)
				
			return weight_one_form(self.chi(),new_possible_hecke,self.space())


	def is_nontrivial(self):
		"""
		Determines if there is some minimal polynomial possible for each computed prime

		INPUT:
		- none

		OUTPUT:
        
		True or False
		"""
		if self.hecke() == {}:
			return False
		bool = true
		for q in self.primes():
			bool = bool and self[q] != []

		return bool



	def unique(self,exclude=[]):
		"""
		Determines if for each eigenvalue there is a unique possible minimal polynomial it satisfies.

		If the form has no eigenvalues, True is returned.

		INPUT:
		- none

		OUTPUT:
        
		True or False
		"""		
		bool = true
		for ell in self.primes():
			if exclude.count(ell) == 0:
				bool = bool and len(self[ell]) == 1

		return bool

	### returns the splitting field of hecke polys
	def FC_field(self):
		assert self.unique(),"not unique in FC_field"

		poly = 1
		for q in self.primes():
			poly *= self[q][0]
		K,phi = poly.splitting_field('a',map=true)
		return K,phi

	### returns the discriminant of the product of all min polys
	def disc(self):
		poly = 1
		for q in self.primes():
			poly *= self[q][0]
		poly = square_free(poly)
		return poly.discriminant().norm()

	def grab_eigens(self,Kf=None,sturm=None,verbose=false):		
		t,pf,phibar,bool = self.space().grab_eigens(0,Kf=Kf,sturm=sturm,verbose=verbose)
		self._phibar = phibar
		self._pf = pf
		assert bool,"uh-oh!"
		self._evs_modp = t

	def lift_eigen_system(self,Kf=None,sturm=None,verbose=false):
		assert self.unique(),"min polys not yet unique"
		if self.evs_modp() == None:
			self.grab_eigens(Kf=Kf,sturm=sturm,verbose=verbose)
		if sturm != None:
			d = len(self.evs_modp().keys())
			max_key = max(self.evs_modp().keys())
			if next_prime(max_key) < sturm:
				self.grab_eigens(Kf=Kf,sturm=sturm,verbose=verbose)
		phibar = self._phibar
		evs_modp = self.evs_modp()
		pf = self._pf
		Kf = pf.ring()
		kf = pf.residue_field()
		p = kf.characteristic()

		ans = {}
		R = PolynomialRing(Kf,'x')
		for q in evs_modp.keys():
#			print "prime ",q
#			print "R =",R
			fq = self.hecke(q,0)
			rs = R(fq).roots()
			done = false
			j = 0
#			print f
#			print " roots",rs
			possible_lifts = [r[0] for r in rs if evs_modp[q] == kf(r[0])]
			assert len(possible_lifts)>0, "no congruent root found "+str(rs)+str(fq)
			assert len(possible_lifts)==1, "lift not unique!"
			ans[q] = possible_lifts[0]

		self._evs = ans

	def an(self,n):
		evs = self.evs()
		chi = self.chi()
		if self.phi() == None:
			Kf = self._pf.ring()
			Kchi = chi(1).parent()
			if Kchi == QQ:
				Kchi = CyclotomicField(2)
			pchi = self.space()._pchi
			pf = self._pf
			kchi = pchi.residue_field()
			kf = pf.residue_field()
			found = false
			r = 0
			H = Hom(Kchi,Kf)
			while not found:
				phi = H[r]
				found = self._phibar(kchi(Kchi.gen())) == kf(phi(Kchi.gen()))
				r += 1
			self._phi = phi
			self._neben = chi.change_ring(phi)
			chi = self._neben
		if n == 1:
			return 1
		else:
			fact = ZZ(n).factor()
			if len(fact) > 1:
				ans = 1
				for f in fact:
					q = f[0]
					e = f[1]
					ans *= self.an(q**e)
				return ans
			else:
				q = fact[0][0]	
				e = fact[0][1]
				if e == 1:
					return evs[q]
				else:
					return self.an(q**(e-1)) * evs[q] - chi(q) * self.an(q**(e-2))

	## takes dictionary on primes to full q-expansion
	def form_q_exp(self,sturm,Kf=None,verbose=false):
		if self.evs() == None:
			self.lift_eigen_system(Kf=Kf,sturm=sturm,verbose=verbose)
		d = len(self.evs().keys())
		max_key = max(self.evs().keys())
		if next_prime(max_key) < sturm:
#			print "finding more evs"
			self.lift_eigen_system(Kf=Kf,sturm=sturm,verbose=verbose)
#			print self.evs()
		evs = self.evs()
		L = evs[evs.keys()[0]].parent()
		R = PowerSeriesRing(L,'q')
		q = R.gens()[0]

		ans = 0
		for n in range(1,sturm):
			ans += self.an(n) * q**n

		self._q_exp = ans 

		
########################################
##  DEFINE THE WEIGHT ONE SPACE CLASS ##
########################################

########################################################################################################
##				
##  Elements of this class store all potential weight 1 forms of a fixed level.
##  The forms are simply stored in a list.  
##  
########################################################################################################
class weight_one_space(SageObject):
	def __init__(self,forms,chi):
		"""
		Returns the space of weight 1 forms consisting of the forms listed in the list "forms".

		INPUT:
		- forms = list of weight_one_form forms

		OUTPUT:
        
		A space of weight one forms.  
		"""
		self._forms = forms
		if len(forms) > 0:
			self._p = forms[0].p()
		else:
			self._p = None
		self._chi = chi

	def chi(self):
		return self._chi

	def p(self):
		return self._p

	def num_forms(self):
		"""
		Returns the number of forms in the space.

		INPUT:
		- none

		OUTPUT:
        
		The number of forms in the space.
		"""
		return len(self._forms)

	def forms(self):
		"""
		Returns a list will all of the forms in the space.

		INPUT:
		- none

		OUTPUT:
        
		A list of all forms in the space.
		"""
		return [self._forms[r] for r in range(self.num_forms())]

	def __getitem__(self,r):
		"""
		Returns the r-th form of the space.

		INPUT:
		- r -- an integer (less than the number of forms in the space)

		OUTPUT:
        
		Returns the r-th form of the space.
		"""
		return self._forms[r]

	def remove(self,f):
		"""
		Removes one copy of the form f from the space

		INPUT:
		- f --- weight one form

		OUTPUT:
        
		None
		"""
		assert self.multiplicity(f) > 0,"Not in space"

		self._forms.remove(f)

	def remove_hecke(self,h):
		"""
		Removes a form with the hecke-eigensystem h

		INPUT:
		- h --- hecke eigensystem (dictionary)

		OUTPUT:
        
		None
		"""
		assert self.hecke_multiplicity(h) > 0,"Not in space"

		self._forms.remove(weight_one_form(0,hecke=h))

	def remove_hecke_completely(self,h):
		"""
		Removes all forms with hecke system h

		INPUT:
		- h --- hecke eigensystem (dictionary)

		OUTPUT:
        
		None
		"""
		assert self.hecke_multiplicity(h) > 0,"Not in space"

		while self.hecke_multiplicity(h) > 0:
			self.remove_hecke(h)

	def level(self):
		"""
		Returns the level of all forms in this space.

		INPUT:
		- none

		OUTPUT:
        
		Returns the level of all forms in this space.
		"""
		return self.form().level()

	def __repr__(self):
		"""
		Displays to the screen all forms in the space.

		I didn't really know how to do this right.

		INPUT:
		- none

		OUTPUT:
		
		Prints to the screen all forms and then just dumps a blank string.
		"""
#		self.display_space()

#		return repr("weight1_space")
		return repr(self.forms())

	def display_space(self):

		for f in self.forms():
			print f

		return None

	def multiplicity(self,f):
		"""
		Returns the number of forms in self identically equal to f.

		INPUT:
		- f -- weight one form

		OUTPUT:
		
		The number of forms in self equal to f.
		"""
		mult = 0
		for i in range(self.num_forms()):
			if self[i] == f:
				mult = mult + 1
		return mult

	def hecke_multiplicity(self,h):
		"""
		Returns the number of forms in self with same hecke min polys as the given data h

		INPUT:
		- h -- dictionary q --> min poly

		OUTPUT:
		
		The number of forms in self with hecke data equal to h
		"""
		mult = 0
		for i in range(self.num_forms()):
			if equal_dicts(self[i].hecke(),h):
				mult = mult + 1
		return mult

	def intersect(self,B):
		"""
		Returns the space of all forms in self which could also occur in B.

		I DONT ACTUAL DO THIS MULTIPLICITY STUFF AT THIS POINT
		For each form in f, its multiplicity is computed.  Then the number of forms in B which compare to f is computed.
		If the multiplicity is higher than the number of forms in B comparing to f, we compute the intersection of f and
		each of these forms in B, and add them to our intersection.
		If this multiplicity is lower, then the intersection of f and the "union" of all forms of B is computed (using
		intersect_with_many).  The result is then added to our intersection with multiplicity equal to the multiplcity of f.

		Note that intersecting self with B is different from intersecting B with self!!

		INPUT:
		- B -- a space of weight one forms.

		OUTPUT:
		
		The subspace of self which could also occur in B.
		"""
		new_forms = []

		for f in self.forms():
			g=f.intersect_with_many(B.forms())
			if g.is_nontrivial():
				new_forms += [g]

		return weight_one_space(new_forms,self.chi())

		# used_up = [False for j in range(self.num_forms())]
		# for r in range(self.num_forms()):
		# 	if not used_up[r]:
		# 		f = self.form(r)
		# 		Bf = [s for s in range(B.num_forms()) if f.compare(B.form(s))]

		# 		many = [B.form(ind) for ind in Bf]
		# 		if self.multiplicity(f) > len(Bf):
		# 			new_forms = new_forms + [f.intersect_with_many(many) for j in range(len(Bf))]
		# 			for j in range(self.num_forms()):
		# 				if self.form(j) == f:
		# 					used_up[j] = True
		# 		elif len(Bf) > 0:
		# 			new_forms = new_forms + [f.intersect_with_many(many)]
		# 			used_up[r] = True

		# A = weight_one_space(new_forms)
		# if self.all_CM_found():
		# 	A._all_CM_found = True
		# return A

	def is_nontrivial(self):
		"""
		Determines if every form in space has some minimal polynomial possible for each computed prime

		INPUT:
		- none

		OUTPUT:
        
		True or False
		"""
		if self.num_forms() == 0:
			return false
		bool = true
		for f in self:
			bool = bool and f.is_nontrivial()

		return bool

	def is_trivial(self):
		return not self.is_nontrivial()

	def unique(self,exclude=[]):
		"""
		Determines if each form in self has all of the min polys of eigenvalues uniquely determined.

		INPUT:
		- none

		OUTPUT:
        
		True or False
		"""
		for f in self.forms():
			if not f.unique(exclude=exclude):
				return False
		return True

	# def set_form(self,j,f):
	# 	"""
	# 	Sets the j-th form of self equal to f.

	# 	INPUT:
	# 	- j -- integer (less than the number of forms of self)
	# 	- f -- a weight one form

	# 	OUTPUT:
        
	# 	none
	# 	"""
	# 	self.form[j] = f

# 	def remove_CM(self):
# 		if self.num_forms() == 0:
# 			return None
# 		sturm = STURM 
# 		p = self.p()
# 		chi = self.chi()
# 		N = chi.modulus()
# 		Nc = chi.conductor()
# 		Nt = N / Nc
# 		bool = true
# 		for d in divisors(Nt):
# #			print "Trying divisor",d,Nc,N
# 			G_old = DirichletGroup(Nc * d)
# 			chi_old = G_old(chi)
# 			chi_old = convert_character_to_database(chi_old)
# 			chi_old = chi_old.minimize_base_ring()
# 			if CM.keys().count(chi_old) != 0:
# 				for f in CM[chi_old]:
# 					eps = f[1]  ## eps is the same as chi_old except its values have already been extended to K_f
# 					f = f[0]
# 					olds = oldforms(f,eps,d,N)
# 					# print "p",self.p()
# 					# print "A",olds
# 					# print "B",self
# 					for g in olds:
# 						m = self.hecke_multiplicity(g[0])
# 						assert m >= g[1],"CM not found!!"
# 						if m == g[1]:
# 							bad = []
# 							for r in range(self.num_forms()):
# 								if self[r].hecke() == g[0]:
# 									bad += [r]
# 							bad.reverse()
# 							for ind in bad:
# 								self.remove(self[ind])
# 						else:
# #							print "WRONG NUMBER OF CM FORMS HERE"
# 							bool = false
# 		return bool

	def remove_old_and_CM(self,log=None,verbose=False):
		if self.num_forms() == 0:
			return None
		sturm = STURM 
		p = self.p()
		chi = self.chi()
		Qchi = chi.base_ring()
		if Qchi == QQ:
			Qchi = CyclotomicField(2)
		N = chi.modulus()
		Nc = chi.conductor()
		Nt = N / Nc
		worked = true
		all_old = []
		for d in divisors(Nt):
			if d % p != 0:
				G_old = DirichletGroup(Nc * d)
				chi_old = G_old(chi)
				chi_old = convert_character_to_database(chi_old)
				chi_old = chi_old.minimize_base_ring()
				if CM.has_key(chi_old) != 0:
					for g in CM[chi_old]:
						f = g[0]
						eps = g[1]  
						phi = g[2]
						olds = oldforms(f,eps,d,N,phi,sturm=strong_sturm)
						all_old = combine(all_old,olds)
						# print "p",self.p()
						# print "A",olds
						# print "B",self
				if d != Nt:
					if len(exotic[chi_old]) != 0:
						for g in exotic[chi_old]:
							f = g[0]
							eps = g[1]  
							phi = g[2]
							olds = oldforms(f,eps,d,N,phi,sturm=strong_sturm)
							all_old = combine(all_old,olds)
							# print "p",self.p()
							# print "A",olds
							# print "B",self
							# print "C",all_olds
		success = true
		for g in all_old:
			h = {}
			for q in g[0].keys():
				h[q] = [minpoly_over(g[0][q],Qchi,g[1])]
			m = self.hecke_multiplicity(h)
			d = max_degree(h,exclude=[p])
			print "A",m
			print "working on",g[0],"--",h
			print "have",m,"copies of this form and am expecting",g[2]
			print self
			assert m >= g[2],"CM/old not found!!"+str(g[0])+"p="+str(p)+str(self)
			if m == g[2]:
				### multiplicity exactly correct so we can throw away these CM forms safely
				output(log,verbose,3,"can safely remove the CM/old form "+str(g[0]))
				self.remove_hecke_completely(truncate(h,sturm))
			else:
				### there are potentially forms congruent to this CM form in weight p which don't come from weight 1
				### but we now be careful and check to the sturm bound to prove this congruence
				print "not enough --- checking up to strong_sturm for CM/old with p =",p
				W = cut_out2(p,chi,phi,g[0],m,sturm=strong_sturm)
				###!! need to deal with p below in exclude -- just bailing on it for now
				if N % p != 0:
					e = 2
				else:
					e = 1
				if floor(W.dimension()/e) *d >= m:
					print "WW",W.dimension(),d,m
				 	output(log,verbose,3,"after careful check removing the CM/old form "+str(g[0]))
				 	self.remove_hecke_completely(truncate(h,sturm))				 	
				else:
				 	print "couldn't remove the CM/old form",g[0]
				 	success = false
		return success


				# D = decompose(W,chi,strong_sturm,[p],p,log=log,verbose=verbose)
				# only_CM = true
				# for j in range(D.num_spaces()):
				# 	print "Checking",D.hecke_polys(j)
				# 	print D.is_CM(j,g[0],phi,strong_sturm)
				# 	only_CM = only_CM and D.is_CM(j,g,phi,strong_sturm)
				# if only_CM:
				# 	output(log,verbose,3,"after careful check removing the CM/old form "+str(g[0]))
				# 	self.remove_hecke_completely(g[0])
				# else:
				# 	print "couldn't remove the CM/old form",g[0]
				# 	return false

def cut_out(p,chi,h,known_mult,sturm=None):
	#### wrong at p -- need x^2-apx+chi(p) or something
#	d = max_degree(h,chi,exclude=[p])
	m = known_mult
	if sturm == None:
		sturm = STURM
	Qchi = chi.base_ring()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	kp = Qchi.prime_above(p).residue_field()
	R = PolynomialRing(kp,'x')
	M = ModularSymbols(chi,p,1,kp).cuspidal_subspace()
	N = chi.modulus()
	if N % p != 0:
		e = 2
	else:
		e = 1
	for q in primes(sturm):
		if q != p or N % p == 0:
			Tq = M.hecke_operator(q)
			M = ((R(h[q][0]).substitute(Tq))**(M.dimension())).kernel()
			print (q,M,m,e,p,N)
			if M.dimension() <= e*m:
				assert M.dimension() == e*m,"hmm"
				break
	return M

def cut_out2(p,chi,phi,f,known_mult,sturm=None):
	#### wrong at p -- need x^2-apx+chi(p) or something
	m = known_mult
	if sturm == None:
		sturm = STURM
	Qchi = chi.base_ring()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	z = Qchi.gen()
	if not pp.has_key((chi,p)):
		pchi = Qchi.prime_above(p)
	else:
		pchi = pp[(chi,p)]
	kchi = pchi.residue_field()
	Kf = f[f.keys()[0]].parent()
	pf = Kf.prime_above(p)
	kf = pf.residue_field()
	H = Hom(kchi,kf)
	for phibar in H:
		if phibar(kchi(z)) == kf(phi(z)):
			break
	chip = chi.change_ring(phibar)
	M = ModularSymbols(chip,p,1,kf).cuspidal_subspace()
	for q in primes(sturm):
		if q != p:
			Tq = M.hecke_operator(q)
			M = ((Tq-kf(f[q]))**(2*m)).kernel()
			print M

	return M





def max_degree(h,exclude=[]):
	return max([h[q][0].degree() for q in h.keys() if exclude.count(q) == 0])

def square_free(f):
	facts = f.factor()
	ans = 1
	for Q in facts:
		ans *= Q[0]

	return ans
	
## f is new in S_1(Nc * d, chi) where Nc is the conductor of chi
##
## returns dictionaries encoding the minpolys of the generalized Hecke-eigensystems mod pp
## which occur in the span of {f(d'z) : d' | N/(Nc * d) } with multiplicities
##
## chi should take values in the field of FC of f
def oldforms(f,chi,d,N,phi,sturm=None):
	Nc = chi.conductor()
	L = f.base_ring()
	Qchi = chi(1).parent()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	R = PolynomialRing(Qchi,'x')
	x = R.gen()
	Nt = N / (Nc * d)
	if sturm == None:
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
					# P = x**2 - f[ell] * x + chi(ell)
					# M = P.splitting_field('a')
					# inc = Hom(L,M)[0]
					# P = P.change_ring(inc)
					# rs = P.roots()
					# p1 = rs[0][0].minpoly()
					# p2 = rs[1][0].minpoly()

					# h1 = deepcopy(t[0])
					# h1[ell] = [p1]
					# new_v += [[h1,t[1]]]

					# h2 = deepcopy(t[0])
					# h2[ell] = [p2]
					# new_v += [[h2,t[1]]]

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

def equal_dicts(a,b):
	A = set(a.keys())
	B = set(b.keys())
	for q in A.intersection(B):
		if a[q] != b[q]:
			return false
	return true

def truncate(d,sturm):
	h = {}
	for q in d.keys():
		if q < sturm:
			h[q] = d[q]
	return h
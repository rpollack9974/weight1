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
		self._pL = None


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
						same = False
				j = j + 1
			return same


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
			g = many[0]
			all_primes = list(set(self.primes()).union(set(g.primes())))

			new_possible_hecke = {}
			for ell in all_primes:
				if ell in self.primes() and ell in g.primes():
					S1 = set(self[ell])
					S2 = set([])
					for h in many:
						S2 = S2.union(set(h[ell]))
					new_possible_hecke[ell] = list(S1.intersection(S2))
				
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



	def unique(self):
		"""
		Determines if for each eigenvalue there is a unique possible minimal polynomial it satisfies.

		If the form has no eigenvalues, True is returned.

		INPUT:
		- none

		OUTPUT:
        
		True or False
		"""		
		if self.num_evals() == 0:
			return True
		else:
			for polys in self.all_possible_hecke():
				if len(polys)>1:
					return False
			return True

	def grab_eigens(self,sturm=None,verbose=false):		
		t,bool = self.space().grab_eigens(0,sturm=sturm,verbose=false)
		assert bool,"uh-oh!"
		self._evs_modp = t

	def lift_eigen_system(self,sturm=None):
		assert self.unique(),"min polys not yet unique"
		if self.evs_modp() == None:
			self.grab_eigens(sturm=sturm)
		if sturm != None:
			d = len(self.evs_modp().keys())
			max_key = max(self.evs_modp().keys())
			if next_prime(max_key) < sturm:
				print "findind more evs_modp",sturm
				self.grab_eigens(sturm=sturm)
				print self.evs_modp()
		evs_modp = self.evs_modp()
		v = self.hecke().values()
		v = [a[0] for a in v]
		Q = prod(list(set(v)))
		L = Q.splitting_field('a')
	#	print "L=",L

		F = evs_modp[2].parent()

		p = F.characteristic()
		pp = L.prime_above(p)
		self._pL = pp
		kL = pp.residue_field()
	#	print "kL =",kL

		phibar = Hom(F,kL)[0]
		self._phibar = phibar
	#	print phi

		ans = {}
		R = PolynomialRing(L,'x')
		for q in evs_modp.keys():
	#		print "prime ",q
	#		print "R =",R
			f = self.hecke(q,0)
			rs = R(f).roots()
			done = false
			j = 0
	#		print f
	#		print " roots",rs
			possible_lifts = [r[0] for r in rs if phibar(evs_modp[q]) == kL(r[0])]
			assert len(possible_lifts)>0, "no congruent root found"
			assert len(possible_lifts)==1, "lift not unique!"
	# 		while not done and j < len(rs):
	# 			alpha = rs[j][0]
	# #			print ev_modp[q],alpha
	# 			done = phi(evs_modp[q]) == kL(alpha)
	# 			j += 1
#			assert done, "no congruent root found!"
			ans[q] = possible_lifts[0]

		self._evs = ans

	def an(self,n):
		evs = self.evs()
		chi = self.chi()
		if self.phi() == None:
			L = self._pL.ring()
			K = chi(1).parent()
			if K == QQ:
				K = CyclotomicField(2)
			pK = self.space()._pK
			pL = self._pL
			kK = pK.residue_field()
			kL = pL.residue_field()
			found = false
			r = 0
			H = Hom(K,L)
			while not found:
				phi = H[r]
				found = self._phibar(kK(K.gen())) == kL(phi(K.gen()))
				r += 1
			self._phi = phi
			self._neben = chi.change_ring(phi)
			chi = self._neben
# 			L = evs[evs.keys()[0]].parent()
# 			K = chi(1).parent()
# 			self._phi = Hom(K,L).an_element()
# #			chi = chi.change_ring(self.phi()) ## should this be changed always?
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
	def form_q_exp(self,sturm):
		if self.evs() == None:
			self.lift_eigen_system(sturm=sturm)
		d = len(self.evs().keys())
		max_key = max(self.evs().keys())
		if next_prime(max_key) < sturm:
			print "finding more evs"
			self.lift_eigen_system(sturm=sturm)
			print self.evs()
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
	def __init__(self,forms):
		"""
		Returns the space of weight 1 forms consisting of the forms listed in the list "forms".

		INPUT:
		- forms = list of weight_one_form forms

		OUTPUT:
        
		A space of weight one forms.  
		"""
		self._forms = forms

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
		Removes the form f from the space

		INPUT:
		- f -- weight_one_form

		OUTPUT:
        
		None
		"""
		assert self.forms().count(f)>0,"Not in space"

		self._forms.remove(f)

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

		return weight_one_space(new_forms)

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
		bool = true
		for f in self:
			bool = bool and f.is_nontrivial()

		return bool

	def unique(self):
		"""
		Determines if each form in self has all of the min polys of eigenvalues uniquely determined.

		INPUT:
		- none

		OUTPUT:
        
		True or False
		"""
		for f in self.forms():
			if not f.unique():
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





	
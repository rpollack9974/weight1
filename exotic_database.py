class mf_data(SageObject):

	def __init__(self):
		self._database = {}

	def __repr__(self):
		return repr("Database of weight 1 exotic forms")

	def database(self):
		return self._database

	def has_key(self,key):
		return self.database().has_key(key)

	def add_data(self,chi,data):
		if self.has_key(chi):
			self._database[chi] += [data]
		else:
			self._database[chi] = [data]

	# i-th form in database
	def form(self,i):
		return self.database()[i][0]

	# nebentype of i-th form in database
	def neben(self,i):
		return self.database()[i][1]

	# map phi: Q(chi) --> K_f of i-th form in database
	def map(self,i):
		return self.database()[i][2]

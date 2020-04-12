import numpy as np
import matplotlib.pyplot as plt
import copy


class RingRoad_Environment():
	"""
	This class sets up and can simulate a set of IDM controlled vehicles, along with
	one reinforcement learning controlled vehicle in a ring-road environment. 
	"""


	def __init__(self,driver_params=[1.0, 1.5, 30.0, 4.0, 1.2, 2.0],
					ring_length=200,
					num_vehicles=22,
					dt=.1):

		self.driver_params = driver_params
		self.ring_length = ring_length
		self.num_vehicles = num_vehicles
		self.state = self.init_state()
		self.state_Record = []
		self.dt = dt



	def init_state(self):
		''' The last indexed vehicle will follow the first indexed vehicle. '''

		s0 = self.driver_params[5]

		positions = np.linspace(0.0,(self.num_vehicles-1)*s0,self.num_vehicles)

		if(positions[-1] >= self.ring_length):
			raise Exception('Too many vehicles for road length. Reduce number of vehicles, or increase road length.')

		spacings = np.ones(np.shape(positions))*s0
		spacings[-1] = self.ring_length-positions[-1]

		speeds = np.zeros(np.shape(positions))

		state = [0.0,positions,spacings,speeds]

		print('State Initialized')

		return state

	def step(self,NN_controller=None):

		new_state = copy.deepcopy(self.state)
		new_state[0] += self.dt

		if(NN_controller is not None):
			#For if there is NN control:
			p = self.state[1][-1]
			v = self.state[3][-1]
			s =  self.state[2][-1]
			v_l = self.state[3][0]
			dv = (v_l-v)

			# This needs to be altered to whatever the correct way to call the controller is:
			accel = NN_controller.acceleration(v,v_l,s)

			# Perform update:
			s_new = s + self.dt*dv
			p_new = p + self.dt*v
			v_new = v + self.dt*accel

			# Should we let controller crash and go backwards?

			if(v_new <0.0): v_new = 0.0

			if(s_new <.3):
				s_new = .3
				v_new = 0.0

			# Reassign
			new_state[1][-1] = p_new
			new_state[3][-1] = v_new
			new_state[2][-1] = s_new

		else:
			p = self.state[1][-1]
			v = self.state[3][-1]
			s =  self.state[2][-1]
			v_l = self.state[3][0]
			dv = v_l - v

			# This needs to be altered to whatever the correct way to call the controller is:
			accel = self.IDM_Accel(v,v_l,s)

			# Perform update:
			s_new = s + self.dt*dv
			p_new = p + self.dt*v
			v_new = v + self.dt*accel

			if(v_new <0.0): v_new = 0.0

			if(s_new <.3):
				s_new = .3
				v_new = 0.0

			# Reassign
			new_state[1][-1] = p_new
			new_state[3][-1] = v_new
			new_state[2][-1] = s_new

		#Update all other drivers.
		for i in range(self.num_vehicles-1):

			p = self.state[1][i]
			v = self.state[3][i]
			s =  self.state[2][i]
			v_l = self.state[3][i+1]
			dv = v_l - v

			# This needs to be altered to whatever the correct way to call the controller is:
			accel = self.IDM_Accel(v,v_l,s)

			# Perform update:
			s_new = s + self.dt*dv
			p_new = p + self.dt*v
			v_new = v + self.dt*accel

			if(v_new <0.0): v_new = 0.0

			if(s_new <.3):
				s_new = .3
				v_new = 0.0

			# Reassign
			new_state[1][i] = p_new
			new_state[3][i] = v_new
			new_state[2][i] = s_new

		return new_state

	def run_episode(self,episode_length=500,NN_controller=None):
		'''For Derek: This is where you need to be able to have your NN controller issue commands'''

		#Start with initial state:
		self.reset_sim()

		while(self.state[0] < episode_length):
			#Perform state:
			new_state = self.step(NN_controller=NN_controller)

			#Append state:
			self.state_Record.append(new_state)

			#Update the state:
			self.state = new_state


		return

	def plot_Timeseries(self):
		times = []
		numSteps = len(self.state_Record)
		positions = []
		speeds = []
		spacings = []
		for t in range(numSteps):
			curr_state = self.state_Record[t]

			p_vals = np.array(curr_state[1])
			s_vals =  np.array(curr_state[2])
			v_vals = np.array(curr_state[3])

			positions.append(p_vals)
			speeds.append(v_vals)
			spacings.append(s_vals)
			times.append(curr_state[0])

		positions = np.array(positions)
		speeds = np.array(speeds)
		spacings = np.array(spacings)
		times = np.array(times)


		plt.figure()

		plt.subplot(311)
		plt.plot(times,positions)
		plt.ylabel('Positions')
		plt.subplot(312)
		plt.plot(times,speeds)
		plt.ylabel('Speeds')
		plt.subplot(313)
		plt.plot(times,spacings)
		plt.ylabel('Spacings')

		plt.show()

		return

	def reset_sim(self):
		self.state = self.init_state()
		self.state_Record = []
		print('Simulation Reset.')
		return

	def IDM_Accel(self,v,v_l,s):
		a = self.driver_params[0]
		b = self.driver_params[1]
		v0 = self.driver_params[2]
		delta = self.driver_params[3]
		T = self.driver_params[4]
		s0 = self.driver_params[5]

		# in order to deal with ZeroDivisionError
		if abs(s) < 1e-3:
			s = 1e-3
		s_star = s0 + np.max([0, v*T - v*(v_l-v)/(2*np.sqrt(a*b))])
		accel = a*(1.0-(v/v0)**delta-(s_star/s)**2.0)

		return accel

	def get_Equilibrium(self):
		a = self.driver_params[0]
		b = self.driver_params[1]
		v0 = self.driver_params[2]
		delta = self.driver_params[3]
		T = self.driver_params[4]
		s0 = self.driver_params[5]

		s_eq = self.ring_length/self.num_vehicles

		v_eq


	def get_State(self):

		return self.state

	def print_State(self):
		print('time: '+str(self.state[0]))
		print('positions:')
		print(self.state[1]%self.ring_length)
		print('spacings:')
		print(self.state[2])
		print('speeds:')
		print(self.state[3])



if __name__ == "__main__":

	ring_sim_env = RingRoad_Environment(num_vehicles=10,ring_length=150)
	# print(ring_sim_env.get_State())
	# new_state = ring_sim_env.step()
	# print(new_state)
	ring_sim_env.run_episode(episode_length=60.0)
	print('Final State:')
	# print(ring_sim_env.state_Record[-1])
	ring_sim_env.print_State()
	ring_sim_env.plot_Timeseries()
	# ring_sim_env.reset_sim()





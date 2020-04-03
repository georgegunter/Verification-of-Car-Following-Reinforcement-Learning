import numpy as np
import matplotlib.pyplot as pt
import copy


class RingRoad_Environment():
	"""
	This class sets up and can simulate a set of IDM controlled vehicles, along with
	one reinforcement learning controlled vehicle in a ring-road environment. 
	"""


	def __init__(self,driver_params=[0.2, 3.0, 30.0, 4.0, 1.2, 2.0],
					ring_length=200,
					num_vehicles=22,
					dt=.1):

		self.driver_params = driver_params
		self.ring_length = ring_length
		self.num_vehicles = num_vehicles
		self.state = self.init_state()
		self.sim_time = 0.0
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

		state = [positions,spacings,speeds]

		print('State Initialized')

		return state

	def step(self,NN_controller=None):

		new_state = copy.deepcopy(self.state)

		if(NN_controller is not None):
			#For if there is NN control:
			p = self.state[0][-1]
			v = self.state[2][-1]
			s =  self.state[1][-1]
			v_l = self.state[2][0]
			dv = (v_l-v)

			# This needs to be altered to whatever the correct way to call the controller is:
			accel = NN_controller.acceleration(v,v_l,s)

			# Perform update:
			s_new = s + self.dt*dv
			p_new = p + self.dt*v
			v_new = v + self.dt*accel

			# Reassign
			new_state[0][-1] = p_new
			new_state[2][-1] = v_new
			new_state[1][-1] = s_new

		else:
			p = self.state[0][-1]
			v = self.state[2][-1]
			s =  self.state[1][-1]
			v_l = self.state[2][0]
			dv = v_l - v

			# This needs to be altered to whatever the correct way to call the controller is:
			accel = self.IDM_Accel(v,v_l,s)

			# Perform update:
			s_new = s + self.dt*dv
			p_new = p + self.dt*v
			v_new = v + self.dt*accel

			# Reassign
			new_state[0][-1] = p_new
			new_state[2][-1] = v_new
			new_state[1][-1] = s_new

		#Update all other drivers.
		for i in range(self.num_vehicles-1):

			p = self.state[0][i]
			v = self.state[2][i]
			s =  self.state[1][i]
			v_l = self.state[2][i+1]
			dv = v_l - v

			# This needs to be altered to whatever the correct way to call the controller is:
			accel = self.IDM_Accel(v,v_l,s)

			# Perform update:
			s_new = s + self.dt*dv
			p_new = p + self.dt*v
			v_new = v + self.dt*accel

			# Reassign
			new_state[0][i] = p_new
			new_state[2][i] = v_new
			new_state[1][i] = s_new

		return new_state

	def run_episode(self,episode_length=500,NN_controller=None):
		'''For Derek: This is where you need to be able to have your NN controller issue commands'''

		#Start with initial state:
		state_records = []
		time_values = [0.0]
		state_records.append(self.state)

		while(self.sim_time < episode_length):
			#Perform state:
			new_state = self.step(NN_controller=NN_controller)
			self.sim_time += self.dt
			time_values.append(self.dt)

			#Append state:
			state_records.append(new_state)

			#Update the state:
			self.state = new_state


		return state_records, time_values

	def plot_space_time_diagram(self,state_records=None,time_values=None,attribute='speed'):

		if((state_records is None) or (time_values is None)):
			raise Exception('Must specify a simulation history in state_records')

		if(attribute == 'speed'):
			speed_measurements = []
			for state in state_records:
				speeds = state[2]
				speed_measurements.append(speeds)

			speed_measurements = np.array()


		

	def reset_sim(self):
		self.state = self.init_state()
		self.sim_time = 0.0
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

	def get_State(self):

		return self.state


if __name__ == "__main__":

	ring_sim_env = RingRoad_Environment(num_vehicles=10,ring_length=100)
	print(ring_sim_env.get_State())
	new_state = ring_sim_env.step()
	print(new_state)
	state_records,time_values = ring_sim_env.run_episode(episode_length=30.0)
	print('Final State:')
	print(state_records[-1])
	ring_sim_env.reset_sim()





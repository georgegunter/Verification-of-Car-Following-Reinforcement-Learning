import numpy as np
import matplotlib.pyplot as pt


class RingRoad_Environment():
	"""
	This class sets up and can simulate a set of IDM controlled vehicles, along with
	one reinforcement learning controlled vehicle in a ring-road environment. 



	"""


	def __init__(self,driver_params=None,ring_length=200,num_vehicles=22,dt=.1):
		self.driver_params = driver_params
		self.ring_length = ring_length
		self.num_vehicles = num_vehicles
		self.state = init_state(self,ring_length,num_vehicles)
		self.sim_time = 0.0
		self.dt = dt



	def init_state(self,ring_length,num_vehicles,driver_params):
		s0 = driver_params[5]

		positions = np.linspace(0.0,(num_vehicles-1)*s0,num_vehicles)

		if(positions[-1] >= ring_length):
			raise Exception('Too many vehicles for road length. Reduce number of vehicles, or increase road length.')

		spacings = np.ones(np.shape(positions))*s0
		spacings[-1] = ring_length-positions[-1]

		speeds = np.zeros(np.shape(positions))


		state = [positions,spacings,speeds]

		return state



	def step(self,NN_accel_step=None):

		new_state = 



		return None


	def step_Reward(self,old_state,new_state):

		return None

	def run_episode(self,episode_length=500,NN_controller=None):
		'''For Derek: This is where you need to be able to have your NN controller issue commands'''

		while(self.sim_time < episode_length):
			# Time step through


		return None


	def IDM_Accel(driver_params,v,v_l,s):
		a = driver_params[0]
		b = driver_params[1]
		v0 = driver_params[2]
		delta = driver_params[3]
		T = driver_params[4]
		s0 = driver_params[5]

		# in order to deal with ZeroDivisionError
		if abs(s) < 1e-3:
            s = 1e-3


		s_star = s0 + np.max(0, v*T - v*(v_l-v)/(2*np.sqrt(a*b)))
		accel = a*(1.0-(v/v0)**delta-(s_star/s)**2.0)

		return accel



	def get_State(self):

		return self.state


if __name__ == "__main__":



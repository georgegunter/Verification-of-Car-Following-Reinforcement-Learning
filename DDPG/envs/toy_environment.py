import numpy as np
import matplotlib.pyplot as plt

class Car_Follow_1D():
    """
    A simplistic environment that models 2 vehicles (leader and follower) along
    a 1D track with first-order dynamics (position and velocity of each vehicle
    is tracked at each frame.) The environment returns at each step the state
    visible by the follower vehicle and expects the control acceleration as input
    """
    
    def __init__(self,sigma = 0.01,crash_penalty = -10000):
        self.car1 = np.array([10,1]) # position, velocity
        self.car2 = np.array([0,0])
        
        # lists to store all states (for episode plotting)
        self.all_car1 = []
        self.all_car2 = []
        self.all_car1.append(self.car1)
        self.all_car2.append(self.car2)
        self.all_rewards = [0]
        self.avg_rewards = [0]
        self.all_vis_states = []
        self.crash_reward = crash_penalty
        # keeps track of number of steps per episode
        self.step = 0
        self.sigma = sigma
        # sets starting info visible to follower car: spacing,vel,delta vel
        self._vis_state = np.array([(self.car1[0]-self.car2[0]),self.car2[1],(self.car2[1]-self.car1[1])])
        self.all_vis_states.append(self._vis_state)
        
    def __call__(self,car2_acc):
        """
        Expects control input from car 2 for timestep t. Calculates state t+1, 
        returns reward, and sets visible state for time t+1
        """
        
        # update car1 position
        car1_acc = np.random.normal(0,self.sigma)
        car1_pos = self.car1[0] + max(0,self.car1[1] + 0.5*car1_acc) # cap to prevent backwards motion
        car1_vel = max(self.car1[1] + car1_acc,0) # cap to prevent backwards motion
        self.car1 = np.array([car1_pos,car1_vel])
        
        # update car2 position
        car2_pos = self.car2[0] + max(0,self.car2[1] + 0.5*car2_acc) # cap to prevent backwards motion
        car2_vel = max(self.car2[1] + car2_acc,0) # cap to prevent backwards motion
        self.car2 = np.array([car2_pos,car2_vel])
        
        #append to history
        self.all_car1.append(self.car1)
        self.all_car2.append(self.car2)
        
        # reward penalizes for difference in velocity, and deviation from spacing of 10
        reward = - abs(self.car1[1]-self.car2[1]) - (self.car1[0]-self.car2[0]-10)**2
        if self.car2[0] > self.car1[0]: # collision
            reward = self.crash_reward
        if (self.car1[0] - self.car2[0]) > 35: # dropoff
            reward = self.crash_reward
        
        
        # flatten reward for some reason
        try:
            reward = reward[0]
        except:
            pass
        
        self.all_rewards.append(reward)
        self.avg_rewards.append(sum(self.all_rewards)/len(self.all_rewards))
        

        
        self._vis_state = np.array([(self.car1[0]-self.car2[0]),self.car2[1],(self.car2[1]-self.car1[1])])
        self.all_vis_states.append(self._vis_state)
        self.step += 1
        
        return self.vis_state,reward,self.step
    
    @property
    def vis_state(self):
        return self._vis_state
    
    @vis_state.setter
    def vis_state(self,new_state):
        self._vis_state = new_state
        
    
    def show_episode(self,close = True):
        plt.style.use("seaborn")
        
        plt.figure(figsize = (30,10))
        plt.title("Single Episode")
        
        for i in range(len(self.all_vis_states)):
            if len(self.all_vis_states[i].shape) == 1:
                self.all_vis_states[i] = self.all_vis_states[i][:,np.newaxis]
        self.all_vis_states = np.array(self.all_vis_states)

        
        for i in range(0,len(self.all_car1)):
            plt.subplot(311)
            plt.scatter(self.all_car1[i][0],1,color = (0.2,0.8,0.2))
            plt.scatter(self.all_car2[i][0],1,color = (0.8,0.2,0.2))
            reward = round(self.all_rewards[i] *1000)/1000.0
            plt.annotate("Reward: {}".format(reward),(self.all_car2[i][0]-5,1))

            center = self.all_car1[i][0]
            plt.xlim([center -50, center + 50])
            plt.xlabel("Position")

            
        
            plt.subplot(312)
            plt.plot(self.all_rewards[:i])
            plt.plot(self.avg_rewards[:i])
            plt.ylabel("Reward")
            plt.xlabel("Timestep")
            plt.xlim([0,len(self.all_rewards)])
            plt.legend(["Reward","Avg Reward thus Far"])
            
            plt.subplot(313)
            plt.plot(self.all_vis_states[:i,0],color = (0.3,0.6,0.3))
            plt.plot(self.all_vis_states[:i,1],color = (0.6,0.3,0.3))
            plt.plot(self.all_vis_states[:i,2],color = (0.3,0.3,0.6))
            plt.ylabel("State Variable Value")
            plt.xlabel("Timestep")
            plt.xlim([0,len(self.all_vis_states)])
            plt.legend(["Spacing","Velocity", "Delta V"])
            
            
            
            plt.draw()
            plt.pause(0.001)
            plt.clf()
        if close:
            plt.close()

if True and __name__ == "__main__":        
    # test code
    env = Car_Follow_1D()
    state = env.vis_state
    for i in range(0,300):
        if state[0] > 10:
            acc = 0.1
            if state[2] > 0:
                acc = acc - state[2]
        else:
            acc = -0.05
        state,reward,step = env(acc)
    env.show_episode()
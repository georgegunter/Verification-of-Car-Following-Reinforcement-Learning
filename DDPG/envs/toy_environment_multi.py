import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mpc
from scipy.ndimage.filters import gaussian_filter1d as filter_gaussian
class Multi_Car_Follow_1D():
    """
    A simplistic environment that models n vehicles (leader and followers) along
    a 1D track with first-order dynamics (position and velocity of each vehicle
    is tracked at each frame.) The environment returns at each step the state
    visible by the follower vehicle and expects the control acceleration as input
    """
    
    def __init__(self,agent_list = ["rand","step_accel"],sigma = 0.01,crash_penalty = -10000):
        self.n_agents = len(agent_list)

        
        self.all_acc =     [np.zeros(self.n_agents)]
        self.all_pos =     [np.arange(10*(self.n_agents-1),-1,-10)]
        self.all_spacing = [np.ones(self.n_agents)*10.0]
        self.all_vel =     [np.zeros(self.n_agents)]
        self.all_dv =      [np.zeros(self.n_agents)]
        self.all_rewards = [0]
        self.all_vel[0][0] = 1
        self.all_dv[0][1] = -1
        
        # store input params
        self.agent_types = agent_list
        self.sigma = sigma
        self.crash_penalty = crash_penalty
        self.step = 0
        
        # initialize state 
        
    def get_actions(self,model = None):
        """
        Generates visible state for each vehicle and queries appropriate action 
        function to get action. Returns a list of actions
        """
        actions = []
        
        for ag in range(self.n_agents):
            # get visible state
            state = np.array([self.all_spacing[-1][ag],self.all_vel[-1][ag],self.all_dv[-1][ag]])
            
            # query agent function for action
            if self.agent_types[ag] == "rand":
                        actions.append(np.random.normal(0,self.sigma))
                        
            elif self.agent_types[ag] == "step_accel":
                if state[0] > 10: #spacing > goal spacing
                            acc = 0.1
                            if state[2] > 0: # dv > 0
                                acc = acc - state[2]
                else:
                    acc = -0.05
                actions.append(acc)
        
            elif self.agent_types[ag] == "RL":
                act = model.choose_action(state,EVAL = False)
                act = (act-0.5)*0.2
                actions.append(act)
                
            elif self.agent_types[ag] == "step":
                if self.step in [200,400]:
                    acc = -0.5
                elif self.step in [300]:
                    acc = 0.5
                else:
                    acc = 0
                actions.append(acc)
                
        return actions
                
                
    def __call__(self,actions):
        """
        Expects control input for each car for timestep t. Calculates state t+1, 
        returns reward, and sets visible state for time t+1
        """
        # accelerations
        self.all_acc.append(actions)
        
        # positions
        positions = np.zeros(self.n_agents)
        for i in range(self.n_agents):
            positions[i] = self.all_pos[-1][i] + max(0,self.all_vel[-1][i]+0.5*actions[i])
        self.all_pos.append(positions)
        
        # velocities
        velocities = np.zeros(self.n_agents)
        for i in range(self.n_agents):
            velocities[i] = max(self.all_vel[-1][i]+actions[i], 0)
        self.all_vel.append(velocities)
        
        # spacings
        spacing = np.zeros(self.n_agents)
        for i in range(self.n_agents):
            if i == 0:
                spacing[i] = 10
            else:
                spacing[i] = self.all_pos[-1][i-1] - self.all_pos[-1][i] 
        self.all_spacing.append(spacing)
        
        # dv
        dv = np.zeros(self.n_agents)
        for i in range(self.n_agents):
            if i == 0: 
                dv[i] = 0
            else:
                dv[i] = self.all_vel[-1][i] - self.all_vel[-1][i-1]
        self.all_dv.append(dv) 
        
        # reward
        REW_WEIGHT = 10
        rew_vel = np.std(self.all_vel[-1]) * REW_WEIGHT
        rew_spacing = np.sum(np.abs(self.all_spacing[-1]-10.0)**2) 
        reward = -rew_vel -rew_spacing
        
        # end of episode penalties
        for i in range(1,self.n_agents):
            if self.all_spacing[-1][i] < 0 or self.all_spacing[-1][i] > 40:
                reward = self.crash_penalty
                break
        self.all_rewards.append(reward)
        
        self.step += 1
        
        # flatten reward for some reason
        try:
            reward = reward[0]
        except:
            pass
        

        return reward,self.step
 
    
    def show_episode(self,close = True,smooth = True):
        plt.style.use("seaborn")
        
        plt.figure(figsize = (40,10))
        plt.title("Single Episode")
        rrange = np.arange(0.4,1.0,0.6/self.n_agents)
        grange = np.arange(0.6,0.699,0.1/self.n_agents)
        brange = np.arange(0.8,0.899,0.1/self.n_agents)
        #colors = np.random.rand(self.n_agents,3)
        colors = np.array([rrange,grange,brange]).transpose()
        try:     
            colors[0,2] = 0
        except:    
            pass
        colors = mpc.hsv_to_rgb(colors)
        
        all_pos = np.array(self.all_pos)
        all_vel = np.array(self.all_vel).transpose()
        if smooth:
            print(all_vel.shape)
            for row in range(1,len(all_vel)):
                all_vel[row] = filter_gaussian(all_vel[row],sigma = 3, truncate = 4.0)
        all_vel = all_vel.transpose()
        for i in range(len(self.all_pos)):
            
            plt.subplot(411)
            for j in range(len(self.all_pos[0])):
                plt.scatter(self.all_pos[i][j],1,color = colors[j])
                
            reward = round(self.all_rewards[i] *1000)/1000.0
            plt.annotate("Reward: {}".format(reward),(self.all_pos[i][1]-5,1.1))

            center = self.all_pos[i][0]
            plt.xlim([center -40*self.n_agents, center + 10])
            plt.xlabel("Position")
        
            plt.subplot(412)
            plt.plot(self.all_rewards[:i])
            plt.ylabel("Reward")
            plt.xlabel("Timestep")
            plt.xlim([0,len(self.all_rewards)])
            plt.legend(["Reward"])
            
            plt.subplot(413)
            legend = []
            for j in range(self.n_agents):
                legend.append("Car {}".format(j))
                plt.plot(all_vel[:i,j],color = colors[j])
            plt.ylabel("Velocity")
            plt.xlabel("Timestep")
            plt.xlim([0,len(self.all_vel)])
            plt.legend(legend)
            
            plt.subplot(414)
            legend = []
            for j in range(self.n_agents):
                legend.append("Car {}".format(j))
                plt.plot(all_pos[:i,j]-all_pos[:i,0],color = colors[j])
            plt.ylabel("Spacing Relative to Lead Vehicle")
            plt.xlabel("Timestep")
            plt.xlim([0,len(self.all_pos)])
            plt.legend(legend)
            
            plt.draw()
            plt.pause(0.0001)
            plt.clf()
        if close:
            plt.close()

if True and __name__ == "__main__":        
    # test code
    agent_list = ["step","step_accel","step_accel","step_accel","step_accel","step_accel"]
    env = Multi_Car_Follow_1D(agent_list = agent_list)
    for i in range(0,300):
        actions = env.get_actions()
        reward,step = env(actions)

    env.show_episode(smooth = True)
from toy_environment import Car_Follow_1D
from ddpg_torch_copy import Agent
#from DDPG_pytorch_phil_tabor.ddpg_torch import Agent

import _pickle as pickle
import random
import numpy as np
import os

# define agent
agent = Agent(alpha=0.00025, beta=0.0025, input_dims=[3], tau=0.002, env=None,
              batch_size=64,  layer1_size=100, layer2_size=50, n_actions=1)
agent.load_models()


crash_penalty = -1000

print ("Starting Episodes")
# for each loop, reset environment with new random seed
for i in range(1000):
    # to create unique episodes
    np.random.seed(i)
    random.seed(i)
    
    # define environment
    env = Car_Follow_1D(sigma = 0.05,crash_penalty = crash_penalty) 
    obs = env.vis_state
    done = False
    score = 0
    while not done:
        act = agent.choose_action(obs,EVAL = True)
        act = (act-0.5)*0.2 # accelerations in range (-0.2,0.2)
        # shift action into reasonable range
        
        new_state,reward,step_counter = env(act)
       
        # set done
        done = 0
        if reward <= crash_penalty or step_counter > 500: # terminal state
            done = 1

        obs = obs.reshape(-1).astype(float)
        new_state = new_state.reshape(-1).astype(float)
        
        # append reward to total score for episode
        score += reward
        obs = new_state
        

    env.show_episode()
        
    print('Episode {} average score: {}'.format(i,score/step_counter))


from envs.environment_multi_with_IDM import Multi_Car_Follow
from ddpg_torch_copy_safe import Agent
#from DDPG_pytorch_phil_tabor.ddpg_torch import Agent

import _pickle as pickle
import random
import numpy as np
import os

# define agent
if True:
    agent = Agent(alpha=0.0003, beta=0.0003, input_dims=[3], tau=0.0001, env=None,
              batch_size=64,  layer1_size=100, layer2_size=50, n_actions=1)
    #agent.load_models()
    best_score = -100000000
    score_history = []

episode_history = []
crash_penalty = -10000
ep_len= 500



print ("Starting Episodes")
# for each loop, reset environment with new random seed
for i in range(10000):
    # to create unique episodes
    np.random.seed(2000+i)
    random.seed(2000+i)
    
    # define environment
    agent_types = ["RL","IDM","IDM","IDM","IDM","IDM","IDM"]
    #agent_types = ["RL","IDM","IDM","IDM","IDM"]
    #agent_types = ["RL","RL","RL","RL","IDM"]
    #agent_types = ["RL", "RL","RL","RL","RL"]
    env = Multi_Car_Follow(sigma = 0.01,
                           idm_params=[1.0, 1.5, 10.0, 4.0, 1.2, 10.0],
                           ring_length = 80,
                           agent_list = agent_types,
                           crash_penalty = crash_penalty,
                           episode_length = ep_len) 
   
    done = False
    score = 0
    
    
    while not done:
        
        obs = np.array([env.all_spacing[-1],env.all_vel[-1],env.all_dv[-1]]).transpose()
        actions = env.get_actions(model = agent)
        reward,step_counter = env(actions)
        new_states = np.array([env.all_spacing[-1],env.all_vel[-1],env.all_dv[-1]]).transpose()
        
        # record the memory of each agent
        for j in range(0,len(new_states)):
            new_state = new_states[j]
            ob = obs[j]
            act = actions[j]
            
            # set done
            done = 0
            if reward <= crash_penalty/ep_len or step_counter > ep_len: # terminal state
                done = 1

            # reshape inputs
            ob = ob.reshape(-1).astype(float)
            new_state = new_state.reshape(-1).astype(float)

            # store memory
            agent.remember(ob, act, reward, new_state, int(done))
        
        # update actor and critic networks
        agent.learn()
        
        # append reward to total score for episode
        score += reward
        
    # at end of episode, store score_history
    score = score/step_counter
    score_history.append(score)
    agent.noise.reset()
    
    # periodically save checkpoints of model states
    if i % 25 == 0:
        
        # store episode history in file
        episode_history.append(env)
        with open(os.path.join("model_current","episode_history{}".format(i)),'wb') as f:
            pickle.dump(episode_history,f)

    if i % 5 == 0:
        env.show_episode()
    
    print('Episode {} average score: {}'.format(i,score))
    
    if  i % 25 == 0:
        best_score = score
        agent.save_models()
        print ("Saved new best model")
        

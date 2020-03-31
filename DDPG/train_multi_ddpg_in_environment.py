from toy_environment_multi import Multi_Car_Follow_1D
from ddpg_torch_copy import Agent
#from DDPG_pytorch_phil_tabor.ddpg_torch import Agent

import _pickle as pickle
import random
import numpy as np
import os

# define agent
agent = Agent(alpha=0.0001, beta=0.001, input_dims=[3], tau=0.002, env=None,
              batch_size=64,  layer1_size=100, layer2_size=50, n_actions=1)
agent.load_models()

score_history = []
episode_history = []
crash_penalty = -100000

print ("Starting Episodes")
# for each loop, reset environment with new random seed
for i in range(1500):
    # to create unique episodes
    np.random.seed(i)
    random.seed(i)
    
    # define environment
    agent_types = ["rand","RL","step_accel","step_accel","step_accel","step_accel"]
    env = Multi_Car_Follow_1D(sigma = 0.01,agent_list = agent_types, crash_penalty = crash_penalty) 
    done = False
    score = 0
    while not done:
        
        obs = np.array([env.all_spacing[-1][1],env.all_vel[-1][1],env.all_dv[-1][1]])
        actions = env.get_actions(model = agent)
        reward,step_counter = env(actions)
        new_state = np.array([env.all_spacing[-1][1],env.all_vel[-1][1],env.all_dv[-1][1]])
        act = actions[1]
        
        # set done
        done = 0
        if reward <= crash_penalty or step_counter > 500: # terminal state
            done = 1

        # reshape inputs
        obs = obs.reshape(-1).astype(float)
        new_state = new_state.reshape(-1).astype(float)

        # store memory
        agent.remember(obs, act, reward, new_state, int(done))
        
        # update actor and critic networks
        agent.learn()
        
        # append reward to total score for episode
        score += reward
        obs = new_state
        
    # at end of episode, store score_history
    score_history.append(score)

    # periodically save checkpoints of model states
    if i % 25 == 0:
        agent.save_models()
        
        # store episode history in file
        episode_history.append(env)
        with open(os.path.join("checkpoints","episode_history"),'wb') as f:
            pickle.dump(episode_history,f)

    if i % 20 == 0:
        env.show_episode()
        
    print('Episode {} average score: {}'.format(i,score/step_counter))

episode_history[-1].show_episode()
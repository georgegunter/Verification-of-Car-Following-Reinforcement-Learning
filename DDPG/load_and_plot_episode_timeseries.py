from envs.environment_multi_with_IDM import Multi_Car_Follow
from ddpg_torch_copy_safe import Agent
import _pickle as pickle

with open("model_current//episode_history",'rb') as f:
    output = pickle.load(f)
    
index = 0
output[index].show_episode()
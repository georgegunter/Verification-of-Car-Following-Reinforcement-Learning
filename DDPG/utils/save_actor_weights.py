from ddpg_torch_copy_safe import Agent
#from DDPG_pytorch_phil_tabor.ddpg_torch import Agent

import numpy as np
import os
from torch import nn
import scipy.io


save_dir = "model_weights_biases"


# load agent
agent = Agent(alpha=0.0001, beta=0.001, input_dims=[3], tau=0.002, env=None,
              batch_size=64,  layer1_size=100, layer2_size=50, n_actions=1)
agent.load_models()

layer_list = []
for layer in agent.actor.modules():
    if isinstance(layer,nn.Linear):
        layer_list.append((str(layer),layer.weight,layer.bias))
        
out_dict = {}        
for i in range(len(layer_list)):
    weights = layer_list[i][1].data.cpu().numpy()
    biases = layer_list[i][2].data.cpu().numpy()
    
    #weight_path = os.path.join("model_arrays",save_dir,"weights{}.mat".format(i))
    #bias_path   = os.path.join("model_arrays",save_dir,"biases{}.mat".format(i))
    out_dict["weights{}".format(i)] = weights
    out_dict["biases{}".format(i)] = biases
    #scipy.io.savemat(weight_path,weights)
    #scipy.io.savemat(bias_path,biases)
    
#scipy.io.savemat(os.path.join("model_arrays",save_dir),out_dict)
scipy.io.savemat(save_dir,out_dict)
    
    
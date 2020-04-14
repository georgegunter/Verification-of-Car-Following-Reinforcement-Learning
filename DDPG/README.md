# DDPG
 Pytorch implementation of deep deterministic policy gradients for reinforcement learning over continuous action spaces, with the following files:

/envs- stores the environments on which models are trained and tested
/models - stores associated files for each model
	specs.txt - gives description of model and training process
	{}_weights_biases.mat - parameter matrices in form readable by Matlab
	<various checkpoints>.pt - Pytorch files used to reload and save models for training and evaluation
/model_current - since the training process overwrites checkpoints, copy the files for the checkpoint you want to use into model_current beforerunning a training or evaluation script
/old - old files that are no longer used but are saved just in case
/utils - various other files such as for writing Matlab-style parameter file
ddpg_torch_copy.py - main code for DDPG repo. Copied from Phil Tabor's repo because I couldn't get the submodule to work correctly
ddpg_torch_copy_safe.py - same as above but with ReLUs and batchnorm removed (Sigmoid replaces ReLU)
evaluate_multicar.py - run this to see how various agents perform in various environments
train_single.py - code used to train a single RL follower car
train_multi.py - code used (thus far unsuccessfully) to train many RL agents in a ring-road style environment
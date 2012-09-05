static __devinit int vpbe_probe(struct platform_device *pdev)
{
	struct vpbe_device *vpbe_dev;
	struct vpbe_config *cfg;
	int ret = -EINVAL;

	if (pdev->dev.platform_data == NULL) {
		v4l2_err(pdev->dev.driver, "No platform data\n");
		return -ENODEV;
	}
	cfg = pdev->dev.platform_data;

	if (!cfg->module_name[0] ||
	    !cfg->osd.module_name[0] ||
	    !cfg->venc.module_name[0]) {
		v4l2_err(pdev->dev.driver, "vpbe display module names not"
			 " defined\n");
		return ret;
	}

	vpbe_dev = devm_kzalloc(&pdev->dev, sizeof(*vpbe_dev), GFP_KERNEL);
	if (vpbe_dev == NULL) {
		v4l2_err(pdev->dev.driver, "Unable to allocate memory"
			 " for vpbe_device\n");
		return -ENOMEM;
	}
	vpbe_dev->cfg = cfg;
	vpbe_dev->ops = vpbe_dev_ops;
	vpbe_dev->pdev = &pdev->dev;

	if (cfg->outputs->num_modes > 0)
		vpbe_dev->current_timings = vpbe_dev->cfg->outputs[0].modes[0];
	else {
		return -ENODEV;
	}

	/* set the driver data in platform device */
	platform_set_drvdata(pdev, vpbe_dev);
	mutex_init(&vpbe_dev->lock);

	return 0;
}

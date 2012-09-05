static int __devinit mxr_probe(struct platform_device *pdev)
{
	struct device *dev = &pdev->dev;
	struct mxr_platform_data *pdata = dev->platform_data;
	struct mxr_device *mdev;
	int ret;

	/* mdev does not exist yet so no mxr_dbg is used */
	dev_info(dev, "probe start\n");

	mdev = devm_kzalloc(&pdev->dev, sizeof *mdev, GFP_KERNEL);
	if (!mdev) {
		mxr_err(mdev, "not enough memory.\n");
		ret = -ENOMEM;
		goto fail;
	}

	/* setup pointer to master device */
	mdev->dev = dev;

	mutex_init(&mdev->mutex);
	spin_lock_init(&mdev->reg_slock);
	init_waitqueue_head(&mdev->event_queue);

	/* acquire resources: regs, irqs, clocks, regulators */
	ret = mxr_acquire_resources(mdev, pdev);
	if (ret)
		goto fail;

	/* configure resources for video output */
	ret = mxr_acquire_video(mdev, mxr_output_conf,
		ARRAY_SIZE(mxr_output_conf));
	if (ret)
		goto fail_resources;

	/* configure layers */
	ret = mxr_acquire_layers(mdev, pdata);
	if (ret)
		goto fail_video;

	pm_runtime_enable(dev);

	mxr_info(mdev, "probe successful\n");
	return 0;

fail_video:
	mxr_release_video(mdev);

fail_resources:
	mxr_release_resources(mdev);

fail_mem:

fail:
	dev_info(dev, "probe failed\n");
	return ret;
}
